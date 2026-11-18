//! handler definitions for the concrete model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::state::{ChangeV, PartialV, FoldedV, PromV, TkV, ObjV, PromiseEffectV, ProtocolEffectV, ProtocolEffectKeyV, TimerEffectV, DocumentBodyV, WorkflowDocumentV, ScheduleDocumentV, StoredDocumentV, Message, LogicV, Proc, PendingV, NoteV, NoteKeyV, JobV, FlightV, CachedV, NodeV, Held, Etag, StoreError, Read, StoreReq, StoreRes, EntryV, StoreV};
use crate::rover::{Pid};
#[cfg(verus_keep_ghost)]
use crate::property_proof::{lemma_min_key_present, lemma_prefix_bounds};
use rover_spec::rover::comm::Time;

use crate::state::{AKey, AArmed, AEntry, ANode, ACommit};

use crate::state::{AJob, AFired, AStep, ASequence, AAct, AAnswer, AOutcome};
use crate::state::{ProductionCachedV, ProductionCacheStatsV, ProductionCacheEntryV, ProductionCacheV};
use crate::state::ProductionTimerEntryV;
use crate::state::{ProductionAnnouncementV, ProductionConfigurationV, ProductionRosterV, ProductionMembersV, ProductionNodeStateV, ProductionRefreshV, ProductionTimerWheelV, ProductionTimersV, ProductionListingV, ProductionFiringV, ProductionWorkingV, ProductionCommittingV, ProductionDoneV, ProductionFireCtxV, ProductionFlightV, ProductionDocumentSlotV, ProductionFlightsV, ProductionWorkV, ProductionStageV, ProductionIssuedV, ProductionProgressV, ProductionPhaseV, ProductionQueuedV, ProductionDebugV, ProductionDebugOpV, ProductionDebugResetV, ProductionDebugSnapV, ProductionDebugTickV, ProductionStateV};
use crate::state::*;
verus! {
pub open spec fn production_protocol_observe(label: rover_spec::rover::RoverSpec::Label<Pid, ProductionWireMessage>)
    -> Seq<Result<echod_types::protocol::TimedBoundaryEvent, rover_spec::rover::comm::BoundaryEvent<Pid, ProductionWireMessage>>> {
    match label {
        rover_spec::rover::RoverSpec::Label::Input { recipient, at, message } => match message {
            ProductionWireMessage::PublicRequest(call) => seq![Ok(echod_types::protocol::TimedBoundaryEvent::Input {
                recipient: (), at, message: echod_types::protocol::TimedMessage::Request(echod_types::protocol::TimedCall {
                    call: echod_types::Call { client: call.client, id: call.id, request: call.request },
                    offered_at: call.now, pinned: call.pinned,
                }),
            })],
            _ => seq![Err(rover_spec::rover::comm::BoundaryEvent::Input { recipient, at, message })],
        },
        rover_spec::rover::RoverSpec::Label::Outside { sender, at, message } => match message {
            ProductionWireMessage::PublicResult { call, response } => {
                let response = match response {
                    Ok(ProductionAnswerData::Step { response, .. }) => Some(response),
                    Err(_) => Some(spec_unavailable(call.request)),
                    Ok(ProductionAnswerData::Debug { .. }) => None,
                };
                match response {
                    Some(response) => seq![Ok(echod_types::protocol::TimedBoundaryEvent::Output {
                        sender: (), at, message: echod_types::protocol::TimedMessage::Output(echod_types::Output::Response { client: call.client, id: call.id, response }),
                    })],
                    None => seq![Err(rover_spec::rover::comm::BoundaryEvent::Output { sender, at, message })],
                }
            },
            ProductionWireMessage::Effect(ProductionEffectData::Send { address, message: dispatch }) => {
                let dispatch = match dispatch {
                    ProductionDispatchData::Execute { task_id, version } => echod_types::Dispatch::Execute { id: task_id, version },
                    ProductionDispatchData::Unblock(promise) => echod_types::Dispatch::Unblock { address, promise },
                };
                seq![Ok(echod_types::protocol::TimedBoundaryEvent::Output { sender: (), at, message: echod_types::protocol::TimedMessage::Output(echod_types::Output::Dispatch(dispatch)) })]
            },
            _ => Seq::empty(),
        },
        _ => Seq::empty(),
    }
}

pub open spec fn production_lift_target(target: ProductionTargetV) -> ProductionTargetData {
    choose|data: ProductionTargetData| data.deep_view() == target
}

pub open spec fn production_request_target(request: Request) -> Option<ProductionTargetV> {
    let named: Option<(Seq<char>, bool)> = match request {
        Request::PromiseGet(q) => Some((q.id@, false)),
        Request::PromiseCreate(q) => Some((q.id@, false)),
        Request::PromiseSettle(q) => Some((q.id@, false)),
        Request::PromiseRegisterCallback(q) => Some((q.awaited@, false)),
        Request::PromiseRegisterListener(q) => Some((q.awaited@, false)),
        Request::TaskGet(q) => Some((q.id@, false)),
        Request::TaskCreate(q) => Some((q.action.id@, false)),
        Request::TaskAcquire(q) => Some((q.id@, false)),
        Request::TaskFulfill(q) => Some((q.id@, false)),
        Request::TaskRelease(q) => Some((q.id@, false)),
        Request::TaskHalt(q) => Some((q.id@, false)),
        Request::TaskContinue(q) => Some((q.id@, false)),
        Request::TaskFence(q) => Some((q.id@, false)),
        Request::TaskFenceCheck(q) => Some((q.id@, false)),
        Request::TaskSuspend(q) => Some((q.id@, false)),
        Request::TaskHeartbeat(q) => if q.tasks@.len() == 0 { None } else { Some((q.tasks@[0].id@, false)) },
        Request::ScheduleGet(q) => Some((q.id@, true)),
        Request::ScheduleCreate(q) => Some((q.id@, true)),
        Request::ScheduleDelete(q) => Some((q.id@, true)),
    };
    match named {
        None => None,
        Some((id, schedule)) => {
            let name = if schedule { id } else { origin(id) };
            if name.len() == 0 { None }
            else if schedule { Some(ProductionTargetV::Schedule(name)) }
            else { Some(ProductionTargetV::Origin(name)) }
        },
    }
}

pub open spec fn production_public_rejection(event: ProcessEvent<Pid, ProductionWireMessage>) -> Option<ProductionWireMessage> {
    match event {
        ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::PublicRequest(call) }
            if production_request_target(call.request) is None =>
            Some(ProductionWireMessage::PublicResult { call, response: Ok(ProductionAnswerData::Step {
                kind: call.kind, corr: call.corr, action_kind: call.action_kind,
                response: Response::Status(StatusRes { status: 400 }),
                why: Some(spec_string("Request data does not name an id"@)),
            }) }),
        _ => None,
    }
}

pub open spec fn production_public_input(call: ProductionPublicCall, internal: u64, now: u64) -> Option<ProductionInput> {
    match production_request_target(call.request) {
    None => None,
    Some(original_target) => {
    let (target, request, then) = production_normalize_admission(original_target, call.request);
    Some(ProductionInput::Request { clock: now, call: ProductionCallData {
        id: internal, kind: call.kind, corr: call.corr, target: production_lift_target(target), request,
        action_kind: call.action_kind, now: call.now, pinned: call.pinned,
        then: match then { None => None, Some((target, request)) => Some((production_lift_target(target), request)) },
    }})
    },
    }
}

pub open spec fn production_public_displace(pending: Seq<ProductionPublicRoute>, internal: u64)
    -> (Seq<ProductionPublicRoute>, Seq<(Pid, ProductionWireMessage)>)
    decreases pending.len(),
{
    if pending.len() == 0 { (Seq::empty(), Seq::empty()) }
    else {
        let (rest, send) = production_public_displace(pending.skip(1), internal);
        if pending[0].internal == internal {
            (rest, seq![(Pid::Outside, ProductionWireMessage::PublicResult {
                call: pending[0].call, response: Err(spec_string("node crashed"@)),
            })] + send)
        } else { (seq![pending[0]] + rest, send) }
    }
}

pub open spec fn production_public_admission(
    next: u64, pending: Seq<ProductionPublicRoute>, event: ProcessEvent<Pid, ProductionWireMessage>,
) -> (u64, Seq<ProductionPublicRoute>, Seq<(Pid, ProductionWireMessage)>) {
    match event {
        ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::PublicRequest(call) } => (
            if next == u64::MAX { 0 } else { (next + 1) as u64 },
            production_public_displace(pending, next).0.push(ProductionPublicRoute { internal: next, call }),
            production_public_displace(pending, next).1,
        ),
        _ => (next, pending, Seq::empty()),
    }
}

pub open spec fn production_pending_index(pending: Seq<ProductionPublicRoute>, internal: u64) -> Option<int>
    decreases pending.len(),
{
    if pending.len() == 0 { None }
    else if pending[0].internal == internal { Some(0) }
    else { match production_pending_index(pending.skip(1), internal) { None => None, Some(i) => Some(i + 1) } }
}

pub open spec fn production_public_outputs(pending: Seq<ProductionPublicRoute>, packets: Seq<(Pid, ProductionWireMessage)>)
    -> (Seq<ProductionPublicRoute>, Seq<(Pid, ProductionWireMessage)>)
    decreases packets.len(),
{
    if packets.len() == 0 { (pending, Seq::empty()) }
    else {
        let (pending, packet) = match packets[0] {
            (Pid::Outside, ProductionWireMessage::Effect(ProductionEffectData::Reply { id, response })) =>
                match production_pending_index(pending, id) {
                    None => (pending, packets[0]),
                    Some(i) => (pending.remove(i), (Pid::Outside, ProductionWireMessage::PublicResult { call: pending[i].call, response })),
                },
            _ => (pending, packets[0]),
        };
        let (pending, rest) = production_public_outputs(pending, packets.skip(1));
        (pending, seq![packet] + rest)
    }
}

pub open spec fn production_normalize_admission(
    target: ProductionTargetV, request: Request,
) -> (ProductionTargetV, Request, Option<(ProductionTargetV, Request)>) {
    match request {
        Request::TaskFence(q) => match q.action {
            TaskFenceAction::Create(create)
                if create.timeout_at <= MAX_TIME && origin(create.id@) != origin(q.id@) => (
                    ProductionTargetV::Origin(origin(create.id@)), Request::PromiseCreate(create),
                    Some((ProductionTargetV::Origin(origin(q.id@)),
                        Request::TaskFenceCheck(TaskFenceCheckReq { id: q.id, version: q.version }))),
                ),
            _ => (target, request, None),
        },
        _ => (target, request, None),
    }
}

pub open spec fn production_delivery_clock(input: ProductionInput, now: u64) -> ProductionInput {
    match input {
        ProductionInput::Request { call, .. } => ProductionInput::Request { clock: now, call },
        ProductionInput::Debug { call, .. } => ProductionInput::Debug { clock: now, call },
        ProductionInput::Store { op, response, .. } => ProductionInput::Store { clock: now, op, response },
        ProductionInput::Wake { armed, .. } => ProductionInput::Wake { clock: now, armed },
    }
}

pub open spec fn production_route_effects(
    wake: Option<(u64, ProductionArmed)>, now: u64, effects: Seq<(Pid, ProductionWireMessage)>,
) -> (Option<(u64, ProductionArmed)>, Seq<(Pid, ProductionWireMessage)>)
    decreases effects.len(),
{
    if effects.len() == 0 {
        (wake, Seq::empty())
    } else {
        let next_wake = match effects[0].1 {
            ProductionWireMessage::Effect(ProductionEffectData::Wake { after_ms, armed }) => Some((spec_sat_add(now, after_ms), armed)),
            _ => wake,
        };
        let message = match effects[0].1 {
            ProductionWireMessage::Effect(ProductionEffectData::Store { op, request }) => (Pid::Store, ProductionWireMessage::StoreCall { op, request }),
            _ => effects[0],
        };
        let (wake, rest) = production_route_effects(next_wake, now, effects.skip(1));
        (wake, seq![message] + rest)
    }
}

pub open spec fn production_routed_input(
    wake: Option<(u64, ProductionArmed)>, next: u64, now: u64, event: ProcessEvent<Pid, ProductionWireMessage>,
) -> Option<(ProductionInput, Option<(u64, ProductionArmed)>)> {
    match event {
        ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::PublicRequest(call) } =>
            match production_public_input(call, next, now) { Some(input) => Some((input, wake)), None => None },
        ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::Input(input) } =>
            match input {
                ProductionInput::Request { .. } | ProductionInput::Debug { .. } =>
                    Some((production_delivery_clock(input, now), wake)),
                _ => None,
            },
        ProcessEvent::Receive { sender: Pid::Store, message: ProductionWireMessage::StoreReply { op, response } } =>
            Some((ProductionInput::Store { clock: now, op, response }, wake)),
        ProcessEvent::Timeout => match wake {
            Some((at, armed)) if at <= now => Some((ProductionInput::Wake { clock: now, armed }, None)),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn production_routed_node_step(
    node: ProductionRoutedNodeV, now: u64, event: ProcessEvent<Pid, ProductionWireMessage>,
) -> Seq<StepResultV<ProductionFleetModel, Pid, ProductionWireMessage>> {
    match production_public_rejection(event) {
        Some(message) => seq![StepResultV { state: ProductionFleetModel::Node(node), send: seq![(Pid::Outside, message)] }],
        None => match production_routed_input(node.wake, node.next_request, now, event) {
        None => Seq::empty(),
        Some((input, wake)) => {
            let (core, effects) = production_handler_spec_on_event(node.node.core, input.deep_view());
            let (wake, send) = production_route_effects(wake, now, effects.map_values(|e: ProductionEffectV|
                (Pid::Outside, ProductionWireMessage::Effect(production_lift_effect(e)))));
            let (next_request, pending, before) = production_public_admission(node.next_request, node.pending, event);
            let (pending, send) = production_public_outputs(pending, send);
            seq![StepResultV {
                state: ProductionFleetModel::Node(ProductionRoutedNodeV { node: ProductionNodeModel { core }, id: node.id, wake, next_request, pending }),
                send: before + send,
            }]
        },
        },
    }
}

pub open spec fn production_store_failure(request: StoreReq, error: String) -> StoreRes {
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

pub open spec fn production_fleet_store_step(
    store: StoreV, fault: Option<String>, event: ProcessEvent<Pid, ProductionWireMessage>,
) -> Seq<StepResultV<ProductionFleetModel, Pid, ProductionWireMessage>> {
    match event {
        ProcessEvent::Receive { sender: Pid::Node(id), message: ProductionWireMessage::StoreCall { op, request } } => {
            let sender = Pid::Node(id);
            if store.seen.contains((sender, op)) {
                seq![StepResultV { state: ProductionFleetModel::Store(store), send: Seq::empty() }]
            } else {
                let (applied, response) = spec_apply(store, request);
                let before = StoreV { seen: store.seen.push((sender, op)), ..store };
                let after = StoreV { seen: store.seen.push((sender, op)), ..applied };
                let normal = StepResultV {
                    state: ProductionFleetModel::Store(after),
                    send: seq![(sender, ProductionWireMessage::StoreReply { op, response })],
                };
                match fault {
                    None => seq![normal],
                    Some(error) => {
                        let send = seq![(sender, ProductionWireMessage::StoreReply { op, response: production_store_failure(request, error) })];
                        seq![normal, StepResultV { state: ProductionFleetModel::Store(before), send },
                            StepResultV { state: ProductionFleetModel::Store(after), send }]
                    },
                }
            }
        },
        _ => Seq::empty(),
    }
}

pub open spec fn production_fleet_step(
    state: ProductionFleetModel, config: ProductionFleetConfig, now: u64,
    event: ProcessEvent<Pid, ProductionWireMessage>,
) -> Seq<StepResultV<ProductionFleetModel, Pid, ProductionWireMessage>> {
    match state {
        ProductionFleetModel::Node(node) => production_routed_node_step(node, now, event),
        ProductionFleetModel::Store(store) => production_fleet_store_step(store, config.fault, event),
    }
}

pub open spec fn production_node_step(
    node: ProductionNodeModel,
    event: ProcessEvent<Pid, ProductionWireMessage>,
) -> Seq<StepResultV<ProductionNodeModel, Pid, ProductionWireMessage>> {
    match event {
        ProcessEvent::Receive { sender: Pid::Outside, message: ProductionWireMessage::Input(input) } => {
            let (core, effects) = production_handler_spec_on_event(node.core, input.deep_view());
            seq![StepResultV {
                state: ProductionNodeModel { core },
                send: effects.map_values(|effect: ProductionEffectV|
                    (Pid::Outside, ProductionWireMessage::Effect(production_lift_effect(effect)))),
            }]
        },
        _ => seq![StepResultV { state: node, send: Seq::empty() }],
    }
}

pub open spec fn production_lift_effect(effect: ProductionEffectV) -> ProductionEffectData {
    choose|data: ProductionEffectData| data.deep_view() == effect
        && crate::property_claim::production_effect_canonical(data)
}

pub open spec fn production_document_data_rows(rows: Seq<(Seq<char>, ObjV)>) -> Map<Seq<char>, ObjV>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Map::empty()
    } else {
        production_document_data_rows(rows.drop_last()).insert(rows.last().0, rows.last().1)
    }
}

pub open spec fn production_replay_state(
    config: ProductionConfigV,
    loops: bool,
    events: Seq<ProductionEventV>,
    count: nat,
) -> ProductionStateV
    recommends count <= events.len(),
    decreases count,
{
    if count == 0 {
        ProductionStateV { loops, ..production_state_spec_state_new(config) }
    } else {
        production_handler_spec_on_event(
            production_replay_state(config, loops, events, (count - 1) as nat),
            events[count as int - 1],
        ).0
    }
}

pub open spec fn production_state_spec_state_new(cfg: ProductionConfigV) -> ProductionStateV {
    ProductionStateV {
        node: production_state_node_spec_node_new(cfg),
        timers: production_state_timers_spec_timers_new(),
        cache: spec_production_cache_new(cfg.cache_entries, cfg.cache_bytes),
        clock: 0,
        tokens: (production_hash(cfg.url + "/"@ + cfg.node_id) as u64) | 1,
        next_op: 1,
        next_flight: 1,
        ops: Map::empty(),
        flights: production_handler_docs_spec_flights_new(),
        debug: production_debug_spec_debug_new(),
        loops: false,
        out: Seq::empty(),
        last_wake: None,
        keys: ProductionKeySpaceV {
            prefix: production_keys_spec_normalize_prefix(cfg.prefix),
            bucket_ms: if cfg.timer_bucket_ms < 1 { 1u64 } else { cfg.timer_bucket_ms },
        },
        cfg,
    }
}

pub open spec fn production_state_spec_now(s: ProductionStateV) -> u64 {
    if s.clock > s.node.fleet_at { s.clock } else { s.node.fleet_at }
}

pub open spec fn production_state_spec_fresh(s: ProductionStateV) -> bool {
    spec_production_fresh(s.node.core, production_state_spec_now(s) as nat)
}

pub open spec fn production_state_spec_acting(s: ProductionStateV) -> bool {
    s.node.core.members.len() != 0 && production_state_spec_fresh(s)
}

pub open spec fn production_state_spec_emit(s: ProductionStateV, e: ProductionEffectV) -> ProductionStateV {
    ProductionStateV { out: s.out.push(e), ..s }
}

pub open spec fn production_state_spec_note(s: ProductionStateV, n: ProductionNoteV) -> ProductionStateV {
    ProductionStateV { out: s.out.push(ProductionEffectV::Note(n)), ..s }
}

pub open spec fn production_state_spec_store(s: ProductionStateV, request: StoreReqSpec, owner: ProductionOwner) -> (ProductionStateV, u64) {
    let op = s.next_op;
    (ProductionStateV {
        next_op: s.next_op.wrapping_add(1),
        ops: s.ops.insert(op, owner),
        out: s.out.push(ProductionEffectV::Store { op, request }),
        ..s
    }, op)
}

pub open spec fn production_state_spec_token(s: ProductionStateV) -> (ProductionStateV, u64) {
    (ProductionStateV { tokens: s.tokens.wrapping_add(0x9e37_79b9_7f4a_7c15), ..s }, s.tokens)
}

pub open spec fn production_state_spec_key_name(s: ProductionStateV, k: AKey, by: Seq<char>) -> Seq<char> {
    if production_verified_text_spec_starts_with(k.origin, "sched:"@) {
        production_keys_spec_sched_timer_key(s.keys.prefix, s.keys.bucket_ms, k.origin.skip(6), k.at as u64, k.token as u64, by)
    } else {
        production_keys_spec_timer_key(s.keys.prefix, s.keys.bucket_ms, k.origin, k.at as u64, k.token as u64, by)
    }
}

pub open spec fn production_state_spec_forget_all(core: ANode, evicted: Seq<Seq<char>>) -> ANode
    decreases evicted.len(),
{
    if evicted.len() == 0 { core } else { production_state_spec_forget_all(spec_production_forget(core, evicted[0]), evicted.drop_first()) }
}

pub open spec fn production_state_spec_remember(s: ProductionStateV, origin: Seq<char>, c: ProductionCachedV) -> ProductionStateV {
    let (evicted, cache) = spec_production_cache_put(s.cache, origin, c);
    let core = production_state_spec_forget_all(s.node.core, evicted);
    let core = spec_production_filled(core, origin, c.etag.0, c.filled_at as nat);
    ProductionStateV { cache, node: ProductionNodeStateV { core, ..s.node }, ..s }
}

pub open spec fn production_state_spec_forget_origin(s: ProductionStateV, origin: Seq<char>) -> ProductionStateV {
    ProductionStateV {
        cache: spec_production_cache_remove(s.cache, origin),
        node: ProductionNodeStateV { core: spec_production_forget(s.node.core, origin), ..s.node },
        ..s
    }
}

pub open spec fn production_state_spec_wake_moved(s: ProductionStateV, next: Option<(u64, ProductionArmed)>) -> (ProductionStateV, bool) {
    if next == s.last_wake { (s, false) } else { (ProductionStateV { last_wake: next, ..s }, true) }
}

pub open spec fn production_state_node_spec_roster_insert(s: Seq<(Seq<char>, ProductionAnnouncementV)>, id: Seq<char>, a: ProductionAnnouncementV) -> Seq<(Seq<char>, ProductionAnnouncementV)>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![(id, a)]
    } else if s[0].0 == id {
        seq![(id, a)] + s.drop_first()
    } else if spec_before(id, s[0].0) {
        seq![(id, a)] + s
    } else {
        seq![s[0]] + production_state_node_spec_roster_insert(s.drop_first(), id, a)
    }
}

pub open spec fn production_state_node_spec_roster_ids(s: Seq<(Seq<char>, ProductionAnnouncementV)>) -> Seq<Seq<char>> {
    s.map_values(|e: (Seq<char>, ProductionAnnouncementV)| e.0)
}

pub open spec fn production_state_node_spec_members_new(cfg: ProductionConfigV) -> ProductionMembersV {
    ProductionMembersV {
        me: ProductionAnnouncementV { id: cfg.node_id, url: cfg.url, at: 0 },
        heartbeat_ms: cfg.heartbeat_ms,
        ttl: cfg.node_ttl_ms,
        nodes: ProductionRosterV { entries: Seq::empty() },
        etag: None,
        next_heartbeat: None,
        refresh: None,
        read_once: false,
    }
}

pub open spec fn production_state_node_spec_node_new(cfg: ProductionConfigV) -> ProductionNodeStateV {
    ProductionNodeStateV {
        core: ANode {
            id: cfg.node_id, ttl: cfg.node_ttl_ms as nat, read_any: false, epoch: 0,
            members: Seq::empty(), last_read: 0, cache: Map::empty(), armed: Map::empty(),
        },
        members: production_state_node_spec_members_new(cfg),
        fleet_at: 0,
    }
}

pub uninterp spec fn production_state_node_spec_announcement_bytes(a: ProductionAnnouncementV) -> Seq<u8>;

pub uninterp spec fn production_state_node_spec_parse_announcement(bytes: Seq<u8>) -> Option<ProductionAnnouncementV>;

pub uninterp spec fn production_state_node_spec_configuration_bytes(c: ProductionConfigurationV) -> Seq<u8>;

pub uninterp spec fn production_state_node_spec_parse_configuration(bytes: Seq<u8>) -> ProductionConfigurationV;

pub open spec fn production_state_timers_spec_slot_before(a: (u64, Seq<char>), b: (u64, Seq<char>)) -> bool {
    a.0 < b.0 || (a.0 == b.0 && spec_before(a.1, b.1))
}

pub open spec fn production_state_timers_spec_arm(s: Set<(u64, Seq<char>)>, at: u64, key: Seq<char>) -> Set<(u64, Seq<char>)> {
    s.insert((at, key))
}

pub open spec fn production_state_timers_spec_disarm(s: Set<(u64, Seq<char>)>, at: u64, key: Seq<char>) -> Set<(u64, Seq<char>)> {
    s.remove((at, key))
}

pub open spec fn production_state_timers_spec_is_first(s: Set<(u64, Seq<char>)>, key: (u64, Seq<char>)) -> bool {
    s.contains(key) && forall|other: (u64, Seq<char>)| s.contains(other)
        ==> !production_state_timers_spec_slot_before(other, key)
}

pub open spec fn production_state_timers_spec_minimum(s: Set<(u64, Seq<char>)>) -> (u64, Seq<char>) {
    choose|key: (u64, Seq<char>)| production_state_timers_spec_is_first(s, key)
}

pub open spec fn production_state_timers_spec_take_due_n(s: Set<(u64, Seq<char>)>, now: u64, fuel: nat)
    -> (Seq<(u64, Seq<char>)>, Set<(u64, Seq<char>)>)
    decreases fuel,
{
    if fuel == 0 || s.is_empty() { (Seq::empty(), s) }
    else {
        let first = production_state_timers_spec_minimum(s);
        if first.0 > now { (Seq::empty(), s) }
        else {
            let (due, rest) = production_state_timers_spec_take_due_n(s.remove(first), now, (fuel - 1) as nat);
            (seq![first] + due, rest)
        }
    }
}

pub open spec fn production_state_timers_spec_take_due(s: Set<(u64, Seq<char>)>, now: u64, limit: nat)
    -> (Seq<(u64, Seq<char>)>, Set<(u64, Seq<char>)>)
{
    production_state_timers_spec_take_due_n(s, now, limit)
}

pub open spec fn production_state_timers_spec_nearest(s: Set<(u64, Seq<char>)>) -> Option<u64> {
    if s.is_empty() { None } else { Some(production_state_timers_spec_minimum(s).0) }
}

pub open spec fn production_state_timers_spec_min_opt(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        (None, None) => None,
    }
}

pub open spec fn production_state_timers_spec_max(a: u64, b: u64) -> u64 {
    if a > b { a } else { b }
}

pub open spec fn production_state_timers_spec_wake_at(t: ProductionTimersV, now: u64) -> Option<u64> {
    let due = if t.loaded_through is Some && t.inflight < CONCURRENCY {
        if t.backlog.len() > 0 { Some(now) } else { production_state_timers_spec_nearest(t.wheel.armed) }
    } else { None };
    if !t.started {
        None
    } else if t.backoff_until is Some {
        production_state_timers_spec_min_opt(due, t.backoff_until)
    } else if t.listing is Some {
        if t.listing->Some_0.ready() { Some(now) } else { due }
    } else if t.reload_pending {
        Some(now)
    } else {
        let closing = match t.closed_through {
            Some(c) => Some(production_state_timers_spec_max(c.saturating_add((2 as u64).saturating_mul(t.bucket_ms)), now)),
            None => None,
        };
        let loaded = match t.loaded_through {
            Some(l) => Some(production_state_timers_spec_max(l, now)),
            None => None,
        };
        production_state_timers_spec_min_opt(due, production_state_timers_spec_min_opt(t.rediscover_at, production_state_timers_spec_min_opt(loaded, closing)))
    }
}

pub open spec fn production_state_timers_spec_timers_new() -> ProductionTimersV {
    ProductionTimersV {
        wheel: ProductionTimerWheelV { armed: Set::empty() },
        started: false,
        loaded_through: None,
        closed_through: None,
        bucket_ms: 0,
        reload_pending: false,
        listing: None,
        backoff_until: None,
        inflight: 0,
        backlog: Seq::empty(),
        budget: 0,
        rediscover_at: None,
    }
}

pub open spec fn production_state_timers_spec_next_wake(t: ProductionTimersV, now: u64) -> Option<(u64, ProductionArmed)> {
    match production_state_timers_spec_wake_at(t, now) {
        Some(at) => Some((at, ProductionArmed::Wheel)),
        None => None,
    }
}

pub open spec fn production_handler_docs_spec_flights_new() -> ProductionFlightsV {
    ProductionFlightsV { slots: Map::empty(), inflight: Map::empty(), max_retries: 8 }
}

pub open spec fn production_handler_docs_spec_empty_slot() -> ProductionDocumentSlotV {
    ProductionDocumentSlotV { busy: None, queue: Seq::empty() }
}

pub open spec fn production_handler_docs_spec_slot_of(s: ProductionStateV, name: Seq<char>) -> ProductionDocumentSlotV {
    if s.flights.slots.contains_key(name) { s.flights.slots[name] } else { production_handler_docs_spec_empty_slot() }
}

pub open spec fn production_handler_docs_spec_with_slot(s: ProductionStateV, name: Seq<char>, slot: ProductionDocumentSlotV) -> ProductionStateV {
    ProductionStateV { flights: ProductionFlightsV { slots: s.flights.slots.insert(name, slot), ..s.flights }, ..s }
}

pub open spec fn production_handler_docs_spec_without_slot(s: ProductionStateV, name: Seq<char>) -> ProductionStateV {
    ProductionStateV { flights: ProductionFlightsV { slots: s.flights.slots.remove(name), ..s.flights }, ..s }
}

pub open spec fn production_handler_docs_spec_inflight(s: ProductionStateV, f: ProductionFlightV) -> ProductionStateV {
    ProductionStateV { flights: ProductionFlightsV { inflight: s.flights.inflight.insert(f.id, f), ..s.flights }, ..s }
}

pub open spec fn production_handler_docs_spec_take_flight(s: ProductionStateV, fid: u64) -> ProductionStateV {
    ProductionStateV { flights: ProductionFlightsV { inflight: s.flights.inflight.remove(fid), ..s.flights }, ..s }
}

pub open spec fn production_handler_docs_spec_dispatch(doc: DocumentBodyV, n: NoteV) -> Option<(Seq<char>, ProductionMessageV)> {
    match n {
        NoteV::Execute { id, version } => {
            if spec_workflow_map(doc).contains_key(id) {
                match production_reason_spec_target_of(spec_workflow_map(doc)[id].promise.tags@) {
                    Some(address) => Some((address, ProductionMessageV::Execute { task_id: id, version })),
                    None => None,
                }
            } else {
                None
            }
        },
        NoteV::Unblock { address, promise } => Some((address, ProductionMessageV::Unblock(promise.deep_view()))),
    }
}

pub open spec fn production_handler_docs_spec_dispatches(doc: DocumentBodyV, notes: Seq<NoteV>) -> Seq<(Seq<char>, ProductionMessageV)>
    decreases notes.len(),
{
    if notes.len() == 0 {
        Seq::empty()
    } else {
        let front = production_handler_docs_spec_dispatches(doc, notes.drop_last());
        match production_handler_docs_spec_dispatch(doc, notes.last()) {
            Some(m) => front.push(m),
            None => front,
        }
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_submit(s: ProductionStateV, target: ProductionTargetV, work: ProductionWorkV, firing: Option<ProductionFiringV>, debug: bool) -> ProductionStateV {
    let name = production_target_spec_name(target);
    let s = match work {
        ProductionWorkV::Sweep { now, .. } => production_state_spec_note(s, ProductionNoteV::SweepBegin { flight: s.next_flight, target: name, now }),
        _ => s,
    };
    let slot = production_handler_docs_spec_slot_of(s, name);
    if slot.busy is Some {
        production_handler_docs_spec_with_slot(s, name, ProductionDocumentSlotV { queue: slot.queue.push(ProductionQueuedV::Work { target, work, firing, debug }), ..slot })
    } else {
        production_handler_docs_spec_start(production_handler_docs_spec_with_slot(s, name, slot), target, work, firing, debug)
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_start(s: ProductionStateV, target: ProductionTargetV, work: ProductionWorkV, firing: Option<ProductionFiringV>, debug: bool) -> ProductionStateV {
    let id = s.next_flight;
    let name = production_target_spec_name(target);
    let slot = production_handler_docs_spec_slot_of(s, name);
    let s = production_handler_docs_spec_with_slot(ProductionStateV { next_flight: id.wrapping_add(1), ..s }, name, ProductionDocumentSlotV { busy: Some(id), ..slot });
    production_handler_docs_spec_begin(s, ProductionFlightV { id, target, work, attempt: 0, phase: ProductionPhaseV::Idle, firing, debug, idle: false })
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_release(s: ProductionStateV, name: Seq<char>) -> ProductionStateV {
    if !s.flights.slots.contains_key(name) {
        s
    } else {
        let slot = s.flights.slots[name];
        if slot.queue.len() == 0 {
            production_handler_docs_spec_without_slot(s, name)
        } else {
            let rest = slot.queue.drop_first();
            match slot.queue[0] {
                ProductionQueuedV::Work { target, work, firing, debug } => {
                    production_handler_docs_spec_start(production_handler_docs_spec_with_slot(s, name, ProductionDocumentSlotV { busy: None, queue: rest }), target, work, firing, debug)
                },
                ProductionQueuedV::Waiter(fid) => production_handler_docs_spec_resume(production_handler_docs_spec_with_slot(s, name, ProductionDocumentSlotV { busy: Some(fid), queue: rest }), fid),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_resume(s: ProductionStateV, fid: u64) -> ProductionStateV {
    if s.flights.inflight.contains_key(fid) {
        let f = s.flights.inflight[fid];
        let s = production_handler_docs_spec_take_flight(s, fid);
        match f.phase {
            ProductionPhaseV::FireWaitingOrigin(ctx) => production_handler_sched_spec_fire_load_origin(s, ProductionFlightV { phase: ProductionPhaseV::Idle, ..f }, ctx),
            _ => production_handler_docs_spec_inflight(s, f),
        }
    } else {
        s
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_begin(s: ProductionStateV, f: ProductionFlightV) -> ProductionStateV {
    match f.work {
        ProductionWorkV::Fire { schedule, .. } => {
            let (s, op) = production_state_spec_store(s, StoreReqSpec::Get { key: production_keys_spec_sched_key(s.keys.prefix, schedule) }, ProductionOwner::Flight(f.id));
            production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireLoadingSchedule { op }, ..f })
        },
        _ => match f.target {
            ProductionTargetV::Origin(o) => {
                let (s, op, revalidating) = production_handler_docs_spec_load_origin(s, f.id, o);
                production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::Loading { op, revalidating }, ..f })
            },
            ProductionTargetV::Schedule(id) => {
                let (s, op) = production_state_spec_store(s, StoreReqSpec::Get { key: production_keys_spec_sched_key(s.keys.prefix, id) }, ProductionOwner::Flight(f.id));
                production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::Loading { op, revalidating: None }, ..f })
            },
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_retry(s: ProductionStateV, f: ProductionFlightV) -> ProductionStateV {
    let f = ProductionFlightV { attempt: f.attempt.wrapping_add(1), ..f };
    if f.attempt > s.flights.max_retries {
        let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Exhausted));
        let what = match f.target {
            ProductionTargetV::Origin(_) => "document"@,
            ProductionTargetV::Schedule(_) => "schedule"@,
        };
        production_handler_docs_spec_fail(s, f, "too many races on the "@ + what)
    } else {
        production_handler_docs_spec_begin(s, f)
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_flight_completed(s: ProductionStateV, fid: u64, op: u64, outcome: StoreRes) -> ProductionStateV {
    if !s.flights.inflight.contains_key(fid) {
        s
    } else {
        let f = s.flights.inflight[fid];
        let s = production_handler_docs_spec_take_flight(s, fid);
        if f.phase.expects() != Some(op) {
            production_handler_docs_spec_inflight(s, f)
        } else {
            production_handler_docs_spec_answered_phase(s, fid, ProductionFlightV { phase: ProductionPhaseV::Idle, ..f }, f.phase, outcome)
        }
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_phase(s: ProductionStateV, fid: u64, f0: ProductionFlightV, phase: ProductionPhaseV, outcome: StoreRes) -> ProductionStateV {
    match phase {
        ProductionPhaseV::Loading { revalidating, .. } => production_handler_docs_spec_answered_loading(s, f0, revalidating, outcome),
        ProductionPhaseV::Origin { commit, done } => production_handler_docs_spec_answered_origin(s, fid, f0, commit, done, outcome),
        ProductionPhaseV::Schedule { commit, done } => production_handler_docs_spec_answered_schedule(s, fid, f0, commit, done, outcome),
        ProductionPhaseV::FireLoadingSchedule { .. } => production_handler_docs_spec_answered_fire_loading_schedule(s, f0, outcome),
        ProductionPhaseV::FireLoadingOrigin { revalidating, ctx, .. } => production_handler_docs_spec_answered_fire_loading_origin(s, f0, revalidating, ctx, outcome),
        ProductionPhaseV::FireIdle { commit } => production_handler_docs_spec_answered_fire_idle(s, fid, f0, commit, outcome),
        ProductionPhaseV::FireOrigin { commit, ctx, t } => production_handler_docs_spec_answered_fire_origin(s, fid, f0, commit, ctx, t, outcome),
        ProductionPhaseV::FireSchedule { commit } => production_handler_docs_spec_answered_fire_schedule(s, fid, f0, commit, outcome),
        _ => production_handler_docs_spec_fail(s, f0, "an answer the flight did not wait for"@),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_loading(s: ProductionStateV, f0: ProductionFlightV, revalidating: Option<ProductionCachedV>, outcome: StoreRes) -> ProductionStateV {
    match f0.target {
        ProductionTargetV::Origin(origin) => {
            let (s, r) = production_handler_docs_spec_loaded_origin(s, origin, revalidating, outcome);
            match r {
                Ok(w) => production_handler_docs_spec_run_origin(s, f0, w),
                Err(e) => production_handler_docs_spec_fail(s, f0, e),
            }
        },
        ProductionTargetV::Schedule(id) => {
            let (s, r) = production_handler_sched_spec_loaded_schedule(s, id, outcome);
            match r {
                Ok(w) => production_handler_sched_spec_run_schedule(s, f0, w),
                Err(e) => production_handler_docs_spec_fail(s, f0, e),
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_origin(s: ProductionStateV, fid: u64, f0: ProductionFlightV, commit: ProductionCommittingV, done: ProductionDoneV, outcome: StoreRes) -> ProductionStateV {
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::Origin { commit, done }, ..f0 }),
        ProductionProgressV::Done(fired) => production_handler_docs_spec_committed(s, f0, done, fired),
        ProductionProgressV::Failed(e) => production_handler_docs_spec_commit_failed(s, f0, e),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_schedule(s: ProductionStateV, fid: u64, f0: ProductionFlightV, commit: ProductionCommittingV, done: ProductionDoneV, outcome: StoreRes) -> ProductionStateV {
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::Schedule { commit, done }, ..f0 }),
        ProductionProgressV::Done(fired) => production_handler_docs_spec_committed(s, f0, done, fired),
        ProductionProgressV::Failed(e) => production_handler_docs_spec_commit_failed(s, f0, e),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_fire_loading_schedule(s: ProductionStateV, f0: ProductionFlightV, outcome: StoreRes) -> ProductionStateV {
    match f0.work {
        ProductionWorkV::Fire { schedule, .. } => {
            let (s, r) = production_handler_sched_spec_loaded_schedule(s, schedule, outcome);
            match r {
                Ok(ws) => production_handler_sched_spec_fire_decide(s, f0, ws),
                Err(e) => production_handler_docs_spec_fail(s, f0, e),
            }
        },
        _ => production_handler_docs_spec_fail(s, f0, "not a fire"@),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_fire_loading_origin(s: ProductionStateV, f0: ProductionFlightV, revalidating: Option<ProductionCachedV>, ctx: ProductionFireCtxV, outcome: StoreRes) -> ProductionStateV {
    let (s, r) = production_handler_docs_spec_loaded_origin(s, ctx.origin, revalidating, outcome);
    match r {
        Ok(wo) => production_handler_sched_spec_fire_run(s, f0, ctx, wo),
        Err(e) => production_handler_docs_spec_fail(production_handler_docs_spec_release(s, ctx.origin), f0, e),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_fire_idle(s: ProductionStateV, fid: u64, f0: ProductionFlightV, commit: ProductionCommittingV, outcome: StoreRes) -> ProductionStateV {
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireIdle { commit }, ..f0 }),
        ProductionProgressV::Done(fired) => {
            let s = production_state_spec_note(s, ProductionNoteV::SweepEnd { flight: fid, committed: true });
            let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Committed));
            production_handler_docs_spec_finish(s, f0, Ok(fired))
        },
        ProductionProgressV::Failed(e) => {
            let s = production_state_spec_note(s, ProductionNoteV::SweepEnd { flight: fid, committed: false });
            production_handler_docs_spec_commit_failed(s, f0, e)
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_fire_origin(s: ProductionStateV, fid: u64, f0: ProductionFlightV, commit: ProductionCommittingV, ctx: ProductionFireCtxV, t: u64, outcome: StoreRes) -> ProductionStateV {
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireOrigin { commit, ctx, t }, ..f0 }),
        ProductionProgressV::Done(_) => {
            let s = production_state_spec_note(s, ProductionNoteV::FireEnd { flight: fid, committed: true });
            let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Committed));
            let s = production_handler_docs_spec_release(s, ctx.origin);
            production_handler_sched_spec_fire_advance(s, f0, ctx, t)
        },
        ProductionProgressV::Failed(e) => {
            let s = production_state_spec_note(s, ProductionNoteV::FireEnd { flight: fid, committed: false });
            let s = production_state_spec_forget_origin(s, ctx.origin);
            let s = production_handler_docs_spec_release(s, ctx.origin);
            production_handler_docs_spec_commit_failed(s, f0, e)
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered_fire_schedule(s: ProductionStateV, fid: u64, f0: ProductionFlightV, commit: ProductionCommittingV, outcome: StoreRes) -> ProductionStateV {
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, fid, commit, Some(outcome));
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireSchedule { commit }, ..f0 }),
        ProductionProgressV::Done(fired) => {
            let s = production_state_spec_note(s, ProductionNoteV::AdvanceEnd { flight: fid, committed: true });
            let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Committed));
            production_handler_docs_spec_finish(s, f0, Ok(fired))
        },
        ProductionProgressV::Failed(e) => {
            let s = production_state_spec_note(s, ProductionNoteV::AdvanceEnd { flight: fid, committed: false });
            production_handler_docs_spec_commit_failed(s, f0, e)
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_load_origin(s: ProductionStateV, fid: u64, origin: Seq<char>) -> (ProductionStateV, u64, Option<ProductionCachedV>) {
    let key = production_keys_spec_doc_key(s.keys.prefix, origin);
    let (cache, hit) = spec_production_cache_get(s.cache, origin);
    let s = ProductionStateV { cache, ..s };
    match hit {
        Some(c) => {
            let (s, op) = production_state_spec_store(s, StoreReqSpec::GetIfNoneMatch { key, etag: c.etag }, ProductionOwner::Flight(fid));
            (s, op, Some(c))
        },
        None => {
            let s = production_state_spec_note(s, ProductionNoteV::Cache(ProductionCacheResult::Miss));
            let (s, op) = production_state_spec_store(s, StoreReqSpec::Get { key }, ProductionOwner::Flight(fid));
            (s, op, None)
        },
    }
}

pub open spec fn production_handler_docs_spec_working(origin: Seq<char>, key: Seq<char>, loaded: LoadedDocumentV, etag: Option<EtagSpec>) -> ProductionWorkingV {
    ProductionWorkingV { target: origin, key, loaded, etag }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_loaded_origin(s: ProductionStateV, origin: Seq<char>, revalidating: Option<ProductionCachedV>, outcome: StoreRes) -> (ProductionStateV, Result<ProductionWorkingV, Seq<char>>) {
    let now = production_state_spec_now(s);
    let key = production_keys_spec_doc_key(s.keys.prefix, origin);
    match revalidating {
        Some(c) => match outcome {
            StoreRes::GetIfNoneMatch { result: Ok(Read::NotModified) } => {
                let s = production_state_spec_note(s, ProductionNoteV::Cache(ProductionCacheResult::Revalidated));
                let s = production_state_spec_remember(s, origin, ProductionCachedV { filled_at: now, ..c });
                (s, Ok(production_handler_docs_spec_working(origin, key, c.loaded, Some(c.etag))))
            },
            StoreRes::GetIfNoneMatch { result: Ok(Read::Absent) } => {
                let s = production_state_spec_note(s, ProductionNoteV::Cache(ProductionCacheResult::Absent));
                let s = production_state_spec_forget_origin(s, origin);
                (s, Ok(production_handler_docs_spec_working(origin, key, production_document_spec_empty_workflow(origin), None)))
            },
            StoreRes::GetIfNoneMatch { result: Ok(Read::Body(bytes, etag)) } => {
                let s = production_state_spec_note(s, ProductionNoteV::Cache(ProductionCacheResult::Refreshed));
                match production_document_spec_decode_workflow(bytes@) {
                    Ok(loaded) => {
                        let s = production_state_spec_remember(s, origin, ProductionCachedV { loaded, etag: etag.deep_view(), filled_at: now });
                        (s, Ok(production_handler_docs_spec_working(origin, key, loaded, Some(etag.deep_view()))))
                    },
                    Err(e) => (s, Err(e)),
                }
            },
            StoreRes::GetIfNoneMatch { result: Err(e) } => (s, Err(production_types_spec_error_text(e.deep_view()))),
            _ => (s, Err(production_types_spec_error_text(production_types_spec_unexpected()))),
        },
        None => match outcome {
            StoreRes::Get { result: Ok(None) } => (s, Ok(production_handler_docs_spec_working(origin, key, production_document_spec_empty_workflow(origin), None))),
            StoreRes::Get { result: Ok(Some((bytes, etag))) } => match production_document_spec_decode_workflow(bytes@) {
                Ok(loaded) => {
                    let s = production_state_spec_remember(s, origin, ProductionCachedV { loaded, etag: etag.deep_view(), filled_at: now });
                    (s, Ok(production_handler_docs_spec_working(origin, key, loaded, Some(etag.deep_view()))))
                },
                Err(e) => (s, Err(e)),
            },
            StoreRes::Get { result: Err(e) } => (s, Err(production_types_spec_error_text(e.deep_view()))),
            _ => (s, Err(production_types_spec_error_text(production_types_spec_unexpected()))),
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_run_origin(s: ProductionStateV, f: ProductionFlightV, w: ProductionWorkingV) -> ProductionStateV {
    let (s, commit, done) = production_handler_docs_spec_decide(s, f.work, w);
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, f.id, commit, None);
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::Origin { commit, done }, ..f }),
        ProductionProgressV::Done(fired) => production_handler_docs_spec_committed(s, f, done, fired),
        ProductionProgressV::Failed(e) => production_handler_docs_spec_commit_failed(s, f, e),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_decide(s: ProductionStateV, work: ProductionWorkV, w: ProductionWorkingV) -> (ProductionStateV, ProductionCommittingV, ProductionDoneV) {
    let now = production_document_spec_clamp_now(production_document_spec_loaded_committed_at(w.loaded), work.now());
    let job = match work {
        ProductionWorkV::Request { req, .. } => AJob::Request(req),
        ProductionWorkV::Sweep { .. } => AJob::Sweep,
        ProductionWorkV::Fire { .. } => AJob::Fire,
    };
    let (after, response, _born, notes) = spec_production_step(job, production_document_spec_loaded_body(w.loaded), now, s.cfg.retry_timeout, REQUEST_SWEEP_STEPS as nat);
    let why = match work {
        ProductionWorkV::Request { req, kind, .. } => match response {
            Some(r) => {
                let status = production_reason_spec_status_of(r@);
                if status >= 400 { Some(production_reason_spec_reason_for(kind, req, status, after)) } else { None }
            },
            None => None,
        },
        _ => None,
    };
    let outbox = production_handler_docs_spec_dispatches(after, notes);
    let deadline = spec_body_deadline(after);
    let fired = match work {
        ProductionWorkV::Sweep { fired, .. } => fired,
        _ => None,
    };
    let (s, commit) = production_handler_docs_spec_commit_new(s, w, after, deadline, now, fired);
    let did = work.is_sweep() && commit.seq.changed;
    (s, commit, ProductionDoneV { response: response.deep_view(), why, outbox, did })
}

pub open spec fn production_handler_docs_spec_send_all(s: ProductionStateV, outbox: Seq<(Seq<char>, ProductionMessageV)>) -> ProductionStateV
    decreases outbox.len(),
{
    if outbox.len() == 0 {
        s
    } else {
        production_handler_docs_spec_send_all(production_state_spec_emit(s, ProductionEffectV::Send { address: outbox[0].0, message: outbox[0].1 }), outbox.drop_first())
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_committed(s: ProductionStateV, f: ProductionFlightV, done: ProductionDoneV, fired: ProductionFired) -> ProductionStateV {
    let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Committed));
    let s = production_handler_docs_spec_send_all(s, done.outbox);
    let s = match f.work {
        ProductionWorkV::Request { id, kind, corr, action_kind, now, stage: ProductionStageV::Detached { then, check }, .. } => {
            match (done.response, check) {
                (Some(AResponse::Promise(inner)), Some(check)) => {
                    let work = ProductionWorkV::Request { id, kind, corr, req: check, action_kind, now, stage: ProductionStageV::Check { inner: Some(inner) } };
                    production_handler_docs_spec_submit(s, then, work, None, f.debug)
                },
                _ => production_state_spec_emit(s, ProductionEffectV::Reply { id, response: Err("no answer"@) }),
            }
        },
        ProductionWorkV::Request { id, kind, corr, action_kind, stage: ProductionStageV::Check { inner }, .. } => {
            let response = match (done.response, inner) {
                (Some(AResponse::Status(st)), Some(inner)) => {
                    let action = if st.status == 200 { Some(echod_types::spec::ATaskFenceInnerRes::Create(inner)) } else { None };
                    Ok(ProductionAnswerV::Step { kind, corr, action_kind, response: AResponse::TaskFence(echod_types::TaskFenceResSpec { status: st.status, action }), why: done.why })
                },
                _ => Err("no answer"@),
            };
            production_state_spec_emit(s, ProductionEffectV::Reply { id, response })
        },
        ProductionWorkV::Request { id, kind, corr, action_kind, stage: ProductionStageV::Whole, .. } => {
            let response = match done.response {
                Some(response) => Ok(ProductionAnswerV::Step { kind, corr, action_kind, response, why: done.why }),
                None => Err("no answer"@),
            };
            production_state_spec_emit(s, ProductionEffectV::Reply { id, response })
        },
        ProductionWorkV::Sweep { .. } => {
            let s = production_state_spec_note(s, ProductionNoteV::Sweep(if done.did { ProductionSweepOutcome::Fired } else { ProductionSweepOutcome::Idle }));
            production_state_spec_note(s, ProductionNoteV::SweepEnd { flight: f.id, committed: true })
        },
        ProductionWorkV::Fire { .. } => s,
    };
    production_handler_docs_spec_finish(s, ProductionFlightV { idle: !done.did, ..f }, Ok(fired))
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_commit_failed(s: ProductionStateV, f: ProductionFlightV, e: StoreErrorSpec) -> ProductionStateV {
    let s = match f.target {
        ProductionTargetV::Origin(o) => production_state_spec_forget_origin(s, o),
        _ => s,
    };
    match e {
        StoreErrorSpec::PreconditionFailed => {
            let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Raced));
            let s = production_state_spec_note(s, ProductionNoteV::Raced { target: production_target_spec_name(f.target), attempt: f.attempt });
            production_handler_docs_spec_retry(s, f)
        },
        _ => {
            let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Failed));
            production_handler_docs_spec_fail(s, f, production_types_spec_error_text(e))
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_fail(s: ProductionStateV, f: ProductionFlightV, e: Seq<char>) -> ProductionStateV {
    let s = match f.work {
        ProductionWorkV::Request { id, .. } => production_state_spec_emit(s, ProductionEffectV::Reply { id, response: Err(e) }),
        ProductionWorkV::Sweep { .. } => {
            let s = production_state_spec_note(s, ProductionNoteV::Sweep(ProductionSweepOutcome::Failed));
            production_state_spec_note(s, ProductionNoteV::SweepEnd { flight: f.id, committed: false })
        },
        ProductionWorkV::Fire { .. } => s,
    };
    production_handler_docs_spec_finish(s, f, Err(e))
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_finish(s: ProductionStateV, f: ProductionFlightV, r: Result<ProductionFired, Seq<char>>) -> ProductionStateV {
    let s = production_handler_docs_spec_release(s, production_target_spec_name(f.target));
    let s = match f.firing {
        Some(firing) => production_handler_timers_spec_timer_fired(s, firing, production_state_spec_now(s), r),
        None => s,
    };
    if f.debug { production_debug_spec_debug_flight_done(s, f.work, f.idle) } else { s }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_commit_new(s: ProductionStateV, w: ProductionWorkingV, after: DocumentBodyV, deadline: Option<nat>, now: u64, fired: Option<AFired>) -> (ProductionStateV, ProductionCommittingV) {
    let changed_any = production_document_spec_loaded_body(w.loaded) != after;
    let etag = match w.etag {
        Some(e) => Some(e.0),
        None => None,
    };
    let (s, token) = production_state_spec_token(s);
    let seq = spec_production_new(s.node.core, w.target, etag, deadline, changed_any, fired, token as nat);
    let after = spec_advance_stored(w.loaded.document, after, now);
    (s, ProductionCommittingV { w, after, now, seq, issued: None })
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_commit_advance(s: ProductionStateV, fid: u64, c: ProductionCommittingV, answer: Option<StoreRes>) -> (ProductionStateV, ProductionCommittingV, ProductionProgressV) {
    let (s, c) = match c.issued {
        Some(issued) => production_handler_docs_spec_answered(s, ProductionCommittingV { issued: None, ..c }, issued, answer),
        None => (s, c),
    };
    let (seq, core, outcome) = spec_production_advance(c.seq, s.node.core, production_answer_v(c.seq.step, answer));
    let s = ProductionStateV { node: ProductionNodeStateV { core, ..s.node }, ..s };
    let c = ProductionCommittingV { seq, ..c };
    match outcome {
        AOutcome::Act(AAct::PutKey(key)) => {
            let name = production_state_spec_key_name(s, key, s.cfg.node_id);
            let (s, op) = production_state_spec_store(s, StoreReqSpec::Put { key: name, body: Seq::empty() }, ProductionOwner::Flight(fid));
            (s, ProductionCommittingV { issued: Some(ProductionIssuedV::Key { op, key, name, arm: true }), ..c }, ProductionProgressV::Issued)
        },
        AOutcome::Act(AAct::Write { cond, idle }) => {
            let (s, c) = production_handler_docs_spec_issue_write(s, fid, c, cond, idle);
            (s, c, ProductionProgressV::Issued)
        },
        AOutcome::Act(AAct::DeleteKey { key, by }) => {
            let name = production_state_spec_key_name(s, key, by);
            let (s, op) = production_state_spec_store(s, StoreReqSpec::Del { key: name }, ProductionOwner::Flight(fid));
            (s, ProductionCommittingV { issued: Some(ProductionIssuedV::Key { op, key, name, arm: false }), ..c }, ProductionProgressV::Issued)
        },
        AOutcome::Act(AAct::Done { deleted }) => (s, c, ProductionProgressV::Done(if deleted { ProductionFired::Deleted } else { ProductionFired::Kept })),
        AOutcome::Failed(Some(e)) => (s, c, ProductionProgressV::Failed(e.deep_view())),
        AOutcome::Failed(None) => (s, c, ProductionProgressV::Failed(production_types_spec_unexpected())),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_answered(s: ProductionStateV, c: ProductionCommittingV, issued: ProductionIssuedV, answer: Option<StoreRes>) -> (ProductionStateV, ProductionCommittingV) {
    match issued {
        ProductionIssuedV::Key { key, name, arm, .. } => match answer {
            Some(StoreRes::Put { result: Ok(()) }) | Some(StoreRes::Del { result: Ok(()) }) => {
                let armed = if arm {
                    production_state_timers_spec_arm(s.timers.wheel.armed, key.at as u64, name)
                } else {
                    production_state_timers_spec_disarm(s.timers.wheel.armed, key.at as u64, name)
                };
                (ProductionStateV { timers: ProductionTimersV { wheel: ProductionTimerWheelV { armed }, ..s.timers }, ..s }, c)
            },
            Some(StoreRes::Put { result: Err(e) }) | Some(StoreRes::Del { result: Err(e) }) => {
                if arm { (s, c) } else { (production_state_spec_note(s, ProductionNoteV::KeyNotDeleted { key: name, error: production_types_spec_error_text(e.deep_view()) }), c) }
            },
            _ => (s, c),
        },
        ProductionIssuedV::Write { mode, change_count, bytes, len, .. } => match answer {
            Some(StoreRes::PutIfMatch { result: Ok(etag) })
            | Some(StoreRes::PutIfNoneMatch { result: Ok(etag) })
            | Some(StoreRes::AppIfMatch { result: Ok(etag) }) => {
                let s = production_state_spec_note(s, ProductionNoteV::DocumentWrite { mode, bytes: len });
                let s = if c.after is Workflow {
                    production_state_spec_remember(s, c.w.target, ProductionCachedV {
                        loaded: LoadedDocumentV {
                            document: c.after,
                            change_count: change_count,
                            bytes,
                        },
                        etag: etag.deep_view(),
                        filled_at: production_state_spec_now(s),
                    })
                } else {
                    s
                };
                (s, ProductionCommittingV { w: ProductionWorkingV { etag: Some(etag.deep_view()), ..c.w }, ..c })
            },
            _ => (s, c),
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_docs_spec_issue_write(s: ProductionStateV, fid: u64, c: ProductionCommittingV, cond: Option<Seq<char>>, idle: bool) -> (ProductionStateV, ProductionCommittingV) {
    let (call, mode, change_count, bytes) = match cond {
        None => {
            let after = spec_stored_body(c.after);
            let body = production_document_spec_encode_body(c.after);
            (StoreReqSpec::PutIfNoneMatch { key: c.w.key, body }, ProductionWriteMode::Create, spec_body_len(after) as usize, body.len() as u64)
        },
        Some(etag) => {
            let etag = EtagSpec(etag);
            let after = spec_stored_body(c.after);
            let (delta, changed) = production_document_spec_encode_delta(c.w.loaded.document, c.after);
            let removed = production_document_spec_removed_any(production_document_spec_loaded_body(c.w.loaded), after);
            let after_len = spec_body_len(after) as usize;
            let stale_after = c.w.loaded.change_count.saturating_add(changed).saturating_sub(after_len);
            let append = production_document_spec_loaded_version(c.w.loaded) > 0 && !removed && s.cfg.appendable && s.cfg.compact > 0 && stale_after < s.cfg.compact as usize;
            if append {
                let n = c.w.loaded.change_count.saturating_add(changed);
                let b = c.w.loaded.bytes.saturating_add(delta.len() as u64);
                (StoreReqSpec::AppIfMatch { key: c.w.key, offset: c.w.loaded.bytes, body: delta, etag }, ProductionWriteMode::Append, n, b)
            } else {
                let body = production_document_spec_encode_body(c.after);
                (StoreReqSpec::PutIfMatch { key: c.w.key, body, etag }, ProductionWriteMode::Rewrite, after_len, body.len() as u64)
            }
        },
    };
    let len = match call {
        StoreReqSpec::PutIfNoneMatch { body, .. } | StoreReqSpec::AppIfMatch { body, .. } | StoreReqSpec::PutIfMatch { body, .. } => body.len() as usize,
        _ => 0usize,
    };
    let (s, op) = production_state_spec_store(s, call, ProductionOwner::Flight(fid));
    (s, ProductionCommittingV { issued: Some(ProductionIssuedV::Write { op, mode, change_count, bytes, len }), ..c })
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_loaded_schedule(s: ProductionStateV, id: Seq<char>, outcome: StoreRes) -> (ProductionStateV, Result<ProductionWorkingV, Seq<char>>) {
    let key = production_keys_spec_sched_key(s.keys.prefix, id);
    let target = production_target_spec_name(ProductionTargetV::Schedule(id));
    match outcome {
        StoreRes::Get { result: Ok(None) } => (s, Ok(production_handler_docs_spec_working(target, key, production_document_spec_empty_schedule(id), None))),
        StoreRes::Get { result: Ok(Some((bytes, etag))) } => match production_document_spec_decode_schedule(bytes@) {
            Ok(loaded) => (s, Ok(production_handler_docs_spec_working(target, key, loaded, Some(etag.deep_view())))),
            Err(e) => (s, Err(e)),
        },
        StoreRes::Get { result: Err(e) } => (s, Err(production_types_spec_error_text(e.deep_view()))),
        _ => (s, Err(production_types_spec_error_text(production_types_spec_unexpected()))),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_run_schedule(s: ProductionStateV, f: ProductionFlightV, w: ProductionWorkingV) -> ProductionStateV {
    let (s, commit, done) = production_handler_docs_spec_decide(s, f.work, w);
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, f.id, commit, None);
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::Schedule { commit, done }, ..f }),
        ProductionProgressV::Done(fired) => production_handler_docs_spec_committed(s, f, done, fired),
        ProductionProgressV::Failed(e) => production_handler_docs_spec_commit_failed(s, f, e),
    }
}

pub open spec fn production_handler_sched_spec_schedule_row(doc: DocumentBodyV) -> Option<echod_types::ScheduleSpec> {
    match doc {
        DocumentBodyV::Schedule(Some(row)) => Some(row.deep_view()),
        _ => None,
    }
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_fire_decide(s: ProductionStateV, f: ProductionFlightV, ws: ProductionWorkingV) -> ProductionStateV {
    match f.work {
        ProductionWorkV::Fire { fired, now, .. } => {
            let t1 = production_document_spec_clamp_now(production_document_spec_loaded_committed_at(ws.loaded), now);
            let body = production_document_spec_loaded_body(ws.loaded);
            let (advanced, _response, born, _notes) = spec_production_step(AJob::Fire, body, t1, s.cfg.retry_timeout, 0);
            let due = match (production_handler_sched_spec_schedule_row(body), born.len() > 0) {
                (Some(row), true) => Some((row, born.last())),
                _ => None,
            };
            match due {
                None => production_handler_sched_spec_fire_idle(s, f, ws, t1, fired),
                Some((row, pending)) => {
                    let next = match production_handler_sched_spec_schedule_row(advanced) {
                        Some(c) => c.next_run_at,
                        None => None,
                    };
                    let origin = echod_types::origin(pending.promise);
                    production_handler_sched_spec_fire_claim(s, f, ProductionFireCtxV { ws, row, advanced, pending, t1, origin, next })
                },
            }
        },
        _ => production_handler_docs_spec_fail(s, f, "not a fire"@),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_fire_idle(s: ProductionStateV, f: ProductionFlightV, ws: ProductionWorkingV, t1: u64, fired: Option<AFired>) -> ProductionStateV {
    let f = ProductionFlightV { idle: true, ..f };
    let body = production_document_spec_loaded_body(ws.loaded);
    let deadline = spec_body_deadline(body);
    let s = production_state_spec_note(s, ProductionNoteV::SweepBegin { flight: f.id, target: ws.target, now: t1 });
    let (s, commit) = production_handler_docs_spec_commit_new(s, ws, body, deadline, t1, fired);
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, f.id, commit, None);
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireIdle { commit }, ..f }),
        ProductionProgressV::Done(fired) => {
            let s = production_state_spec_note(s, ProductionNoteV::SweepEnd { flight: f.id, committed: true });
            let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Committed));
            production_handler_docs_spec_finish(s, f, Ok(fired))
        },
        ProductionProgressV::Failed(e) => {
            let s = production_state_spec_note(s, ProductionNoteV::SweepEnd { flight: f.id, committed: false });
            production_handler_docs_spec_commit_failed(s, f, e)
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_fire_claim(s: ProductionStateV, f: ProductionFlightV, ctx: ProductionFireCtxV) -> ProductionStateV {
    let origin = ctx.origin;
    let slot = production_handler_docs_spec_slot_of(s, origin);
    if slot.busy is Some {
        let s = production_handler_docs_spec_with_slot(s, origin, ProductionDocumentSlotV { queue: slot.queue.push(ProductionQueuedV::Waiter(f.id)), ..slot });
        production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireWaitingOrigin(ctx), ..f })
    } else {
        let s = production_handler_docs_spec_with_slot(s, origin, ProductionDocumentSlotV { busy: Some(f.id), ..slot });
        production_handler_sched_spec_fire_load_origin(s, f, ctx)
    }
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_fire_load_origin(s: ProductionStateV, f: ProductionFlightV, ctx: ProductionFireCtxV) -> ProductionStateV {
    let (s, op, revalidating) = production_handler_docs_spec_load_origin(s, f.id, ctx.origin);
    production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireLoadingOrigin { op, revalidating, ctx }, ..f })
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_fire_run(s: ProductionStateV, f: ProductionFlightV, ctx: ProductionFireCtxV, wo: ProductionWorkingV) -> ProductionStateV {
    let t = production_document_spec_clamp_now(production_document_spec_loaded_committed_at(wo.loaded), ctx.t1);
    let (after, _r, _b, _n) = spec_production_step(AJob::Occurrence(ctx.pending), production_document_spec_loaded_body(wo.loaded), t, s.cfg.retry_timeout, 0);
    let deadline = spec_body_deadline(after);
    let s = production_state_spec_note(s, ProductionNoteV::FireBegin { flight: f.id, origin: ctx.origin, now: t, row: ctx.row, at: ctx.pending.at, promise_id: ctx.pending.promise, next: ctx.next });
    let (s, commit) = production_handler_docs_spec_commit_new(s, wo, after, deadline, t, None);
    let (s, commit, p) = production_handler_docs_spec_commit_advance(s, f.id, commit, None);
    match p {
        ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireOrigin { commit, ctx, t }, ..f }),
        ProductionProgressV::Done(_) => {
            let s = production_state_spec_note(s, ProductionNoteV::FireEnd { flight: f.id, committed: true });
            let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Committed));
            let s = production_handler_docs_spec_release(s, ctx.origin);
            production_handler_sched_spec_fire_advance(s, f, ctx, t)
        },
        ProductionProgressV::Failed(e) => {
            let s = production_state_spec_note(s, ProductionNoteV::FireEnd { flight: f.id, committed: false });
            let s = production_state_spec_forget_origin(s, ctx.origin);
            let s = production_handler_docs_spec_release(s, ctx.origin);
            production_handler_docs_spec_commit_failed(s, f, e)
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_sched_spec_fire_advance(s: ProductionStateV, f: ProductionFlightV, ctx: ProductionFireCtxV, t: u64) -> ProductionStateV {
    match f.work {
        ProductionWorkV::Fire { schedule, fired, .. } => {
            let s = production_state_spec_note(s, ProductionNoteV::AdvanceBegin { flight: f.id, schedule, now: t, at: ctx.pending.at, next: ctx.next });
            let deadline = spec_body_deadline(ctx.advanced);
            let (s, commit) = production_handler_docs_spec_commit_new(s, ctx.ws, ctx.advanced, deadline, t, fired);
            let (s, commit, p) = production_handler_docs_spec_commit_advance(s, f.id, commit, None);
            match p {
                ProductionProgressV::Issued => production_handler_docs_spec_inflight(s, ProductionFlightV { phase: ProductionPhaseV::FireSchedule { commit }, ..f }),
                ProductionProgressV::Done(fired) => {
                    let s = production_state_spec_note(s, ProductionNoteV::AdvanceEnd { flight: f.id, committed: true });
                    let s = production_state_spec_note(s, ProductionNoteV::Commit(ProductionCommitOutcome::Committed));
                    production_handler_docs_spec_finish(s, f, Ok(fired))
                },
                ProductionProgressV::Failed(e) => {
                    let s = production_state_spec_note(s, ProductionNoteV::AdvanceEnd { flight: f.id, committed: false });
                    production_handler_docs_spec_commit_failed(s, f, e)
                },
            }
        },
        _ => production_handler_docs_spec_fail(s, f, "not a fire"@),
    }
}

pub open spec fn production_handler_timers_spec_horizon(s: ProductionStateV, now: u64) -> u64 {
    production_keys_spec_bucket_of(now.saturating_add(s.keys.bucket_ms), s.keys.bucket_ms)
}

pub open spec fn production_handler_timers_spec_owns(s: ProductionStateV, target: Seq<char>) -> bool {
    spec_production_owner(s.node.core.members, target) == Some(s.cfg.node_id)
}

pub open spec fn production_handler_timers_spec_owns_entry(s: ProductionStateV, e: ProductionTimerEntryV) -> bool {
    production_handler_timers_spec_owns(s, e.target())
}

pub open spec fn production_handler_timers_spec_owns_key(s: ProductionStateV, key: Seq<char>) -> bool {
    match production_keys_spec_parse_timer_key(key) {
        Some(e) => production_handler_timers_spec_owns_entry(s, e),
        None => false,
    }
}

pub open spec fn production_handler_timers_spec_with_timers(s: ProductionStateV, t: ProductionTimersV) -> ProductionStateV {
    ProductionStateV { timers: t, ..s }
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_timers_start(s: ProductionStateV, now: u64) -> ProductionStateV {
    let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { started: true, bucket_ms: s.keys.bucket_ms, reload_pending: true, ..s.timers });
    production_handler_timers_spec_timers_run(s, now)
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_timers_membership_changed(s: ProductionStateV) -> ProductionStateV {
    production_handler_timers_spec_with_timers(s, ProductionTimersV { reload_pending: true, ..s.timers })
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_timers_run(s: ProductionStateV, now: u64) -> ProductionStateV {
    if !s.timers.started {
        s
    } else if s.timers.backoff_until is Some && now < s.timers.backoff_until->Some_0 {
        if s.timers.loaded_through is Some { production_handler_timers_spec_fire_due(s, now) } else { s }
    } else {
        let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { backoff_until: None, ..s.timers });
        if s.timers.listing is Some {
            let listing = s.timers.listing->Some_0;
            let cleared = production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: None, ..s.timers });
            let s = match listing {
                ProductionListingV::Scan { scan } => production_handler_timers_spec_advance_scan(cleared, scan, now, 32),
                ProductionListingV::Applying { keys, loaded, after } => production_handler_timers_spec_apply_listing(cleared, keys, loaded, after, now, 32),
                ProductionListingV::Retry { after } => production_handler_timers_spec_start_bucket(cleared, after),
                _ => s,
            };
            if s.timers.loaded_through is Some { production_handler_timers_spec_fire_due(s, now) } else { s }
        } else if s.timers.reload_pending || (s.timers.rediscover_at is Some && s.timers.rediscover_at->Some_0 <= now) {
            production_handler_timers_spec_reload(s, now)
        } else if s.timers.loaded_through is Some && s.timers.loaded_through->Some_0 < production_handler_timers_spec_horizon(s, now) {
            let bucket = s.timers.loaded_through->Some_0.saturating_add(s.keys.bucket_ms);
            let (s, op) = production_state_spec_store(s, StoreReqSpec::List { prefix: production_keys_spec_bucket_prefix(s.keys.prefix, bucket), max_keys: usize::MAX }, ProductionOwner::Timers);
            production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Extend { op, bucket }), ..s.timers })
        } else if s.timers.closed_through is Some && s.timers.closed_through->Some_0.saturating_add(s.keys.bucket_ms) < production_keys_spec_bucket_of(now, s.keys.bucket_ms) {
            let bucket = s.timers.closed_through->Some_0.saturating_add(s.keys.bucket_ms);
            let (s, op) = production_state_spec_store(s, StoreReqSpec::List { prefix: production_keys_spec_bucket_prefix(s.keys.prefix, bucket), max_keys: usize::MAX }, ProductionOwner::Timers);
            production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Relist { op, bucket }), ..s.timers })
        } else if s.timers.loaded_through is Some {
            production_handler_timers_spec_fire_due(s, now)
        } else {
            s
        }
    }
}

pub open spec fn production_handler_timers_spec_reload(s: ProductionStateV, now: u64) -> ProductionStateV {
    let horizon = production_handler_timers_spec_horizon(s, now);
    let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { rediscover_at: Some(now.saturating_add(s.cfg.timer_rediscovery_ms)), reload_pending: true, ..s.timers });
    let (s, op) = production_state_spec_store(s, StoreReqSpec::ListPrefixes { prefix: production_keys_spec_timer_prefix(s.keys.prefix) }, ProductionOwner::Timers);
    production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Prefixes { op, horizon }), ..s.timers })
}

pub open spec fn production_handler_timers_spec_start_bucket(s: ProductionStateV, after: ProductionAfterListingV) -> ProductionStateV {
    let bucket = match after {
        ProductionAfterListingV::Scan { bucket, .. } | ProductionAfterListingV::Extend { bucket } | ProductionAfterListingV::Relist { bucket } => bucket,
    };
    let (s, op) = production_state_spec_store(s, StoreReqSpec::List { prefix: production_keys_spec_bucket_prefix(s.keys.prefix, bucket), max_keys: usize::MAX }, ProductionOwner::Timers);
    let listing = match after {
        ProductionAfterListingV::Scan { bucket, scan } => ProductionListingV::Bucket { op, bucket, scan },
        ProductionAfterListingV::Extend { bucket } => ProductionListingV::Extend { op, bucket },
        ProductionAfterListingV::Relist { bucket } => ProductionListingV::Relist { op, bucket },
    };
    production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(listing), ..s.timers })
}

pub open spec fn production_handler_timers_spec_advance_scan(s: ProductionStateV, scan: ProductionTimerScanV, now: u64, fuel: nat) -> ProductionStateV
    decreases fuel,
{
    if scan.prefixes.len() == 0 {
        production_handler_timers_spec_reloaded(s, scan.horizon, scan.loaded, now)
    } else if fuel == 0 || s.timers.budget == 0 {
        production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Scan { scan }), ..s.timers })
    } else {
        let prefix = scan.prefixes.last();
        let scan = ProductionTimerScanV { prefixes: scan.prefixes.drop_last(), ..scan };
        let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { budget: (s.timers.budget - 1) as usize, ..s.timers });
        match production_keys_spec_parse_bucket_prefix(s.keys.prefix, prefix) {
            Some(bucket) => if bucket <= scan.horizon {
                production_handler_timers_spec_start_bucket(s, ProductionAfterListingV::Scan { bucket, scan })
            } else {
                production_handler_timers_spec_advance_scan(s, scan, now, (fuel - 1) as nat)
            },
            None => production_handler_timers_spec_advance_scan(s, scan, now, (fuel - 1) as nat),
        }
    }
}

pub open spec fn production_handler_timers_spec_finish_listing(s: ProductionStateV, after: ProductionAfterListingV, loaded: usize, now: u64) -> ProductionStateV {
    match after {
        ProductionAfterListingV::Scan { scan, .. } => {
            let scan = ProductionTimerScanV { loaded: scan.loaded.saturating_add(loaded), ..scan };
            if scan.prefixes.len() == 0 { production_handler_timers_spec_reloaded(s, scan.horizon, scan.loaded, now) }
            else { production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Scan { scan }), ..s.timers }) }
        },
        ProductionAfterListingV::Extend { bucket } | ProductionAfterListingV::Relist { bucket } => {
            let s = production_state_spec_note(s, ProductionNoteV::BucketLoaded { bucket, deadlines: loaded });
            let s = production_state_spec_note(s, ProductionNoteV::TimerListing { ok: true });
            match after {
                ProductionAfterListingV::Extend { .. } => production_handler_timers_spec_with_timers(s, ProductionTimersV { loaded_through: Some(bucket), ..s.timers }),
                _ => production_handler_timers_spec_with_timers(s, ProductionTimersV { closed_through: Some(bucket), ..s.timers }),
            }
        },
    }
}

pub open spec fn production_handler_timers_spec_apply_listing(s: ProductionStateV, keys: Seq<Seq<char>>, loaded: usize, after: ProductionAfterListingV, now: u64, fuel: nat) -> ProductionStateV
    decreases fuel,
{
    if keys.len() == 0 {
        production_handler_timers_spec_finish_listing(s, after, loaded, now)
    } else if fuel == 0 || s.timers.budget == 0 {
        production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Applying { keys, loaded, after }), ..s.timers })
    } else {
        let key = keys.last();
        let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { budget: (s.timers.budget - 1) as usize, ..s.timers });
        let (s, loaded) = match production_keys_spec_parse_timer_key(key) {
            Some(entry) => if production_handler_timers_spec_owns_entry(s, entry) {
                (production_handler_timers_spec_with_timers(s, ProductionTimersV { wheel: ProductionTimerWheelV { armed: production_state_timers_spec_arm(s.timers.wheel.armed, entry.deadline(), key) }, ..s.timers }), loaded.saturating_add(1))
            } else { (s, loaded) },
            None => (s, loaded),
        };
        production_handler_timers_spec_apply_listing(s, keys.drop_last(), loaded, after, now, (fuel - 1) as nat)
    }
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_timers_completed(s: ProductionStateV, op: u64, outcome: StoreRes) -> ProductionStateV {
    match s.timers.listing {
        None => s,
        Some(listing) => {
            if !listing.expects(op) {
                s
            } else {
                let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: None, ..s.timers });
                let now = production_state_spec_now(s);
                match listing {
                    ProductionListingV::Prefixes { horizon, .. } => production_handler_timers_spec_prefixes_listed(s, horizon, now, outcome),
                    ProductionListingV::Bucket { bucket, scan, .. } => production_handler_timers_spec_bucket_listed(s, ProductionAfterListingV::Scan { bucket, scan }, now, outcome),
                    ProductionListingV::Extend { bucket, .. } => production_handler_timers_spec_bucket_listed(s, ProductionAfterListingV::Extend { bucket }, now, outcome),
                    ProductionListingV::Relist { bucket, .. } => production_handler_timers_spec_bucket_listed(s, ProductionAfterListingV::Relist { bucket }, now, outcome),
                    _ => s,
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_prefixes_listed(s: ProductionStateV, horizon: u64, now: u64, outcome: StoreRes) -> ProductionStateV {
    match outcome {
        StoreRes::ListPrefixes { result: Ok(prefixes) } => {
            let scan = ProductionTimerScanV { prefixes: prefixes.deep_view(), horizon, loaded: 0 };
            let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Scan { scan }), ..s.timers });
            production_handler_timers_spec_timers_run(s, now)
        },
        StoreRes::ListPrefixes { result: Err(e) } => production_handler_timers_spec_listing_failed(s, e.deep_view(), now),
        _ => production_handler_timers_spec_listing_failed(s, production_types_spec_unexpected(), now),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_bucket_listed(s: ProductionStateV, after: ProductionAfterListingV, now: u64, outcome: StoreRes) -> ProductionStateV {
    match outcome {
        StoreRes::List { result: Ok(keys) } => {
            let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Applying { keys: keys.deep_view(), loaded: 0, after }), ..s.timers });
            production_handler_timers_spec_timers_run(s, now)
        },
        StoreRes::List { result: Err(e) } => {
            let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Retry { after }), ..s.timers });
            production_handler_timers_spec_listing_failed(s, e.deep_view(), now)
        },
        _ => {
            let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { listing: Some(ProductionListingV::Retry { after }), ..s.timers });
            production_handler_timers_spec_listing_failed(s, production_types_spec_unexpected(), now)
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_reloaded(s: ProductionStateV, horizon: u64, loaded: usize, now: u64) -> ProductionStateV {
    let s = production_handler_timers_spec_with_timers(s, ProductionTimersV {
        loaded_through: Some(horizon),
        closed_through: Some(production_keys_spec_bucket_of(now, s.keys.bucket_ms).saturating_sub(s.keys.bucket_ms)),
        reload_pending: false,
        ..s.timers
    });
    let s = production_state_spec_note(s, ProductionNoteV::TimerListing { ok: true });
    production_state_spec_note(s, ProductionNoteV::TimersLoaded { deadlines: loaded, wheel: s.timers.wheel.armed.len() as usize, epoch: s.node.core.epoch as u64 })
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_listing_failed(s: ProductionStateV, e: StoreErrorSpec, now: u64) -> ProductionStateV {
    let s = production_state_spec_note(s, ProductionNoteV::TimerListing { ok: false });
    let s = production_state_spec_note(s, ProductionNoteV::ListingFailed { error: production_types_spec_error_text(e) });
    production_handler_timers_spec_with_timers(s, ProductionTimersV { backoff_until: Some(now.saturating_add(RELIST_AFTER_MS)), ..s.timers })
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_fire_due(s: ProductionStateV, now: u64) -> ProductionStateV {
    let limit = if s.timers.inflight < CONCURRENCY && s.timers.backlog.len() == 0 { s.timers.budget / 2 } else { 0 };
    let (due, rest) = production_state_timers_spec_take_due(s.timers.wheel.armed, now, limit as nat);
    let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { wheel: ProductionTimerWheelV { armed: rest }, backlog: s.timers.backlog + due, budget: (s.timers.budget - due.len()) as usize, ..s.timers });
    production_handler_timers_spec_dispatch_due(s, now, s.timers.backlog.len())
}

pub open spec fn production_handler_timers_spec_dispatch_due(s: ProductionStateV, now: u64, fuel: nat) -> ProductionStateV
    decreases fuel,
{
    if fuel > 0 && s.timers.budget > 0 && s.timers.inflight < CONCURRENCY && s.timers.backlog.len() > 0 {
        let (at, key) = s.timers.backlog[0];
        let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { backlog: s.timers.backlog.drop_first(), budget: (s.timers.budget - 1) as usize, ..s.timers });
        production_handler_timers_spec_dispatch_due(production_handler_timers_spec_timer_fire(s, key, at, now), now, (fuel - 1) as nat)
    } else {
        s
    }
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_timer_fire(s: ProductionStateV, key: Seq<char>, at: u64, now: u64) -> ProductionStateV {
    match production_keys_spec_parse_timer_key(key) {
        None => production_state_spec_note(s, ProductionNoteV::KeyUnparseable { key }),
        Some(entry) => {
            let kind = match entry {
                ProductionTimerEntryV::Origin { .. } => ProductionTimerKind::Origin,
                ProductionTimerEntryV::Schedule { .. } => ProductionTimerKind::Schedule,
            };
            let lag = now.saturating_sub(at);
            let owns = production_handler_timers_spec_owns_entry(s, entry);
            if !owns || !spec_production_acts(s.node.core, entry.target(), now as nat) {
                let s = if owns {
                    production_handler_timers_spec_with_timers(s, ProductionTimersV { wheel: ProductionTimerWheelV { armed: production_state_timers_spec_arm(s.timers.wheel.armed, production_state_timers_spec_max(now, at).saturating_add(RETRY_AFTER_MS), key) }, ..s.timers })
                } else {
                    s
                };
                production_state_spec_note(s, ProductionNoteV::TimerFire { kind, outcome: ProductionFireOutcome::Deferred, lag_ms: lag })
            } else {
                let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { inflight: s.timers.inflight.saturating_add(1), ..s.timers });
                let firing = ProductionFiringV { key, at, kind, lag };
                match entry {
                    ProductionTimerEntryV::Origin { origin, deadline, token, by } => {
                        let fired = AFired { key: AKey { origin, at: deadline as nat, token: token as nat }, by };
                        production_handler_docs_spec_submit(s, ProductionTargetV::Origin(origin), ProductionWorkV::Sweep { fired: Some(fired), now }, Some(firing), false)
                    },
                    ProductionTimerEntryV::Schedule { id, deadline, token, by } => {
                        let fired = AFired { key: AKey { origin: "sched:"@ + id, at: deadline as nat, token: token as nat }, by };
                        production_handler_docs_spec_submit(s, ProductionTargetV::Schedule(id), ProductionWorkV::Fire { schedule: id, fired: Some(fired), now }, Some(firing), false)
                    },
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_timers_spec_timer_fired(s: ProductionStateV, firing: ProductionFiringV, now: u64, r: Result<ProductionFired, Seq<char>>) -> ProductionStateV {
    let s = production_handler_timers_spec_with_timers(s, ProductionTimersV { inflight: s.timers.inflight.saturating_sub(1), ..s.timers });
    let rearm = production_state_timers_spec_max(now, firing.at).saturating_add(RETRY_AFTER_MS);
    let (s, outcome) = match r {
        Ok(ProductionFired::Deleted) => (s, ProductionFireOutcome::Deleted),
        Ok(ProductionFired::Kept) => (production_handler_timers_spec_with_timers(s, ProductionTimersV { wheel: ProductionTimerWheelV { armed: production_state_timers_spec_arm(s.timers.wheel.armed, rearm, firing.key) }, ..s.timers }), ProductionFireOutcome::Kept),
        Err(e) => {
            let s = production_state_spec_note(s, ProductionNoteV::FireFailed { key: firing.key, error: e });
            (production_handler_timers_spec_with_timers(s, ProductionTimersV { wheel: ProductionTimerWheelV { armed: production_state_timers_spec_arm(s.timers.wheel.armed, rearm, firing.key) }, ..s.timers }), ProductionFireOutcome::Failed)
        },
    };
    let s = production_state_spec_note(s, ProductionNoteV::TimerFire { kind: firing.kind, outcome, lag_ms: firing.lag });
    production_handler_timers_spec_dispatch_due(s, now, s.timers.backlog.len())
}

pub open spec fn production_handler_node_spec_with_members(s: ProductionStateV, m: ProductionMembersV) -> ProductionStateV {
    ProductionStateV { node: ProductionNodeStateV { members: m, ..s.node }, ..s }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_members_refresh(s: ProductionStateV, now: u64) -> ProductionStateV {
    if s.node.members.refreshing() {
        s
    } else {
        let me = ProductionAnnouncementV { at: now, ..s.node.members.me };
        let s = production_handler_node_spec_with_members(s, ProductionMembersV { me, ..s.node.members });
        let body = production_state_node_spec_announcement_bytes(me);
        let key = production_keys_spec_node_key(s.keys.prefix, me.id);
        let (s, op) = production_state_spec_store(s, StoreReqSpec::Put { key, body }, ProductionOwner::Members);
        production_handler_node_spec_with_members(s, ProductionMembersV { refresh: Some(ProductionRefreshV::Announcing { op, now }), ..s.node.members })
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_members_tick(s: ProductionStateV, now: u64) -> ProductionStateV {
    let due = match s.node.members.next_heartbeat {
        Some(t) => t <= now,
        None => true,
    };
    if !s.node.members.refreshing() && due { production_handler_node_spec_members_refresh(s, now) } else { s }
}

pub open spec fn production_handler_node_spec_read_nodes(s: ProductionStateV, keys: Seq<Seq<char>>, pending: Map<u64, bool>) -> (ProductionStateV, Map<u64, bool>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (s, pending)
    } else {
        let key = keys[0];
        let (s, pending) = if production_keys_spec_node_of_key(s.keys.prefix, key) == Some(s.node.members.me.id) {
            (s, pending)
        } else {
            let (s, op) = production_state_spec_store(s, StoreReqSpec::Get { key }, ProductionOwner::Members);
            (s, pending.insert(op, true))
        };
        production_handler_node_spec_read_nodes(s, keys.drop_first(), pending)
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_members_completed(s: ProductionStateV, op: u64, outcome: StoreRes) -> ProductionStateV {
    match s.node.members.refresh {
        None => s,
        Some(refresh) => {
            if !refresh.expects(op) {
                s
            } else {
                let s = production_handler_node_spec_with_members(s, ProductionMembersV { refresh: None, ..s.node.members });
                match refresh {
                    ProductionRefreshV::Announcing { now, .. } => production_handler_node_spec_announced(s, now, outcome),
                    ProductionRefreshV::Listing { now, .. } => production_handler_node_spec_listed(s, now, outcome),
                    ProductionRefreshV::Reading { pending, nodes, now, failed } => production_handler_node_spec_read_one(s, pending.remove(op), nodes, now, failed, outcome),
                    ProductionRefreshV::Config { nodes, .. } => production_handler_node_spec_configured(s, nodes, outcome),
                    ProductionRefreshV::Writing { next, .. } => production_handler_node_spec_written(s, next, outcome),
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_announced(s: ProductionStateV, now: u64, outcome: StoreRes) -> ProductionStateV {
    match outcome {
        StoreRes::Put { result: Ok(()) } => {
            let (s, op) = production_state_spec_store(s, StoreReqSpec::List { prefix: production_keys_spec_node_prefix(s.keys.prefix), max_keys: 10_000 }, ProductionOwner::Members);
            production_handler_node_spec_with_members(s, ProductionMembersV { refresh: Some(ProductionRefreshV::Listing { op, now }), ..s.node.members })
        },
        StoreRes::Put { result: Err(e) } => production_handler_node_spec_refresh_ended(s, Err(e.deep_view())),
        _ => production_handler_node_spec_refresh_ended(s, Err(production_types_spec_unexpected())),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_listed(s: ProductionStateV, now: u64, outcome: StoreRes) -> ProductionStateV {
    match outcome {
        StoreRes::List { result: Ok(keys) } => {
            let nodes = ProductionRosterV { entries: production_state_node_spec_roster_insert(Seq::empty(), s.node.members.me.id, s.node.members.me) };
            let (s, pending) = production_handler_node_spec_read_nodes(s, keys.deep_view(), Map::empty());
            if pending =~= Map::<u64, bool>::empty() {
                production_handler_node_spec_read_configuration(s, nodes)
            } else {
                production_handler_node_spec_with_members(s, ProductionMembersV { refresh: Some(ProductionRefreshV::Reading { pending, nodes, now, failed: None }), ..s.node.members })
            }
        },
        StoreRes::List { result: Err(e) } => production_handler_node_spec_refresh_ended(s, Err(e.deep_view())),
        _ => production_handler_node_spec_refresh_ended(s, Err(production_types_spec_unexpected())),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_read_one(s: ProductionStateV, pending: Map<u64, bool>, nodes: ProductionRosterV, now: u64, failed: Option<StoreErrorSpec>, outcome: StoreRes) -> ProductionStateV {
    let (s, nodes, failed) = match outcome {
        StoreRes::Get { result: Ok(Some((bytes, _))) } => match production_state_node_spec_parse_announcement(bytes@) {
            Some(a) => {
                let fleet_at = if s.node.fleet_at > a.at { s.node.fleet_at } else { a.at };
                let s = ProductionStateV { node: ProductionNodeStateV { fleet_at, ..s.node }, ..s };
                if a.at.saturating_add(s.node.members.ttl) >= now {
                    (s, ProductionRosterV { entries: production_state_node_spec_roster_insert(nodes.entries, a.id, a) }, failed)
                } else if a.at.saturating_add((2 as u64).saturating_mul(s.node.members.ttl)) < now {
                    let key = production_keys_spec_node_key(s.keys.prefix, a.id);
                    let (s, _op) = production_state_spec_store(s, StoreReqSpec::Del { key }, ProductionOwner::Ignored);
                    (s, nodes, failed)
                } else {
                    (s, nodes, failed)
                }
            },
            None => (s, nodes, failed),
        },
        StoreRes::Get { result: Ok(None) } => (s, nodes, failed),
        StoreRes::Get { result: Err(e) } => (s, nodes, Some(e.deep_view())),
        _ => (s, nodes, Some(production_types_spec_unexpected())),
    };
    if !(pending =~= Map::<u64, bool>::empty()) {
        production_handler_node_spec_with_members(s, ProductionMembersV { refresh: Some(ProductionRefreshV::Reading { pending, nodes, now, failed }), ..s.node.members })
    } else {
        match failed {
            Some(e) => production_handler_node_spec_refresh_ended(s, Err(e)),
            None => production_handler_node_spec_read_configuration(s, nodes),
        }
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_configured(s: ProductionStateV, nodes: ProductionRosterV, outcome: StoreRes) -> ProductionStateV {
    match outcome {
        StoreRes::Get { result: Ok(read) } => {
            let (config, etag) = match read {
                Some((bytes, etag)) => (production_state_node_spec_parse_configuration(bytes@), Some(etag.deep_view())),
                None => (ProductionConfigurationV { epoch: 0, members: Seq::empty() }, None),
            };
            production_handler_node_spec_take_on(s, config, etag, nodes)
        },
        StoreRes::Get { result: Err(e) } => production_handler_node_spec_refresh_ended(s, Err(e.deep_view())),
        _ => production_handler_node_spec_refresh_ended(s, Err(production_types_spec_unexpected())),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_written(s: ProductionStateV, next: ProductionConfigurationV, outcome: StoreRes) -> ProductionStateV {
    match outcome {
        StoreRes::PutIfMatch { result: Ok(_) } | StoreRes::PutIfNoneMatch { result: Ok(_) } => {
            let s = production_state_spec_note(s, ProductionNoteV::ConfigurationWrite(ProductionConfigWrite::Written));
            let s = production_state_spec_note(s, ProductionNoteV::ConfigurationWritten { epoch: next.epoch, members: next.members });
            production_handler_node_spec_refresh_ended(s, Ok(()))
        },
        StoreRes::PutIfMatch { result: Err(StoreError::PreconditionFailed) }
        | StoreRes::PutIfNoneMatch { result: Err(StoreError::PreconditionFailed) } => {
            let s = production_state_spec_note(s, ProductionNoteV::ConfigurationWrite(ProductionConfigWrite::Conflict));
            production_handler_node_spec_refresh_ended(s, Ok(()))
        },
        StoreRes::PutIfMatch { result: Err(e) } | StoreRes::PutIfNoneMatch { result: Err(e) } => {
            let s = production_state_spec_note(s, ProductionNoteV::ConfigurationWrite(ProductionConfigWrite::Failed));
            production_handler_node_spec_refresh_ended(s, Err(e.deep_view()))
        },
        _ => production_handler_node_spec_refresh_ended(s, Err(production_types_spec_unexpected())),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_read_configuration(s: ProductionStateV, nodes: ProductionRosterV) -> ProductionStateV {
    let (s, op) = production_state_spec_store(s, StoreReqSpec::Get { key: production_keys_spec_members_key(s.keys.prefix) }, ProductionOwner::Members);
    production_handler_node_spec_with_members(s, ProductionMembersV { refresh: Some(ProductionRefreshV::Config { op, nodes }), ..s.node.members })
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_take_on(s: ProductionStateV, config: ProductionConfigurationV, etag: Option<EtagSpec>, nodes: ProductionRosterV) -> ProductionStateV {
    let now = production_state_spec_now(s);
    let changed = !(s.node.core.read_any && s.node.core.epoch == config.epoch as nat);
    let s = if changed { production_state_spec_note(s, ProductionNoteV::ConfigurationRead { epoch: config.epoch, members: config.members }) } else { s };
    let core = spec_production_read_config(s.node.core, now as nat, config.epoch as nat, config.members);
    let s = ProductionStateV { node: ProductionNodeStateV { core, members: ProductionMembersV { nodes, etag, ..s.node.members }, ..s.node }, ..s };
    let s = if changed {
        let s = production_state_spec_note(s, ProductionNoteV::ConfigurationChange);
        production_handler_timers_spec_timers_membership_changed(s)
    } else {
        s
    };
    production_handler_node_spec_write_members(s, config, etag, nodes)
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_write_members(s: ProductionStateV, config: ProductionConfigurationV, etag: Option<EtagSpec>, nodes: ProductionRosterV) -> ProductionStateV {
    let live = production_state_node_spec_roster_ids(nodes.entries);
    if live != config.members {
        let next = ProductionConfigurationV { epoch: config.epoch.saturating_add(1), members: live };
        let body = production_state_node_spec_configuration_bytes(next);
        let key = production_keys_spec_members_key(s.keys.prefix);
        let call = match etag {
            Some(etag) => StoreReqSpec::PutIfMatch { key, body, etag },
            None => StoreReqSpec::PutIfNoneMatch { key, body },
        };
        let (s, op) = production_state_spec_store(s, call, ProductionOwner::Members);
        production_handler_node_spec_with_members(s, ProductionMembersV { refresh: Some(ProductionRefreshV::Writing { op, next }), ..s.node.members })
    } else {
        production_handler_node_spec_refresh_ended(s, Ok(()))
    }
}

pub open spec fn production_handler_node_spec_ended(r: Result<(), StoreError>) -> Result<(), StoreErrorSpec> {
    match r {
        Ok(()) => Ok(()),
        Err(e) => Err(e.deep_view()),
    }
}

#[verifier::opaque]
pub open spec fn production_handler_node_spec_refresh_ended(s: ProductionStateV, r: Result<(), StoreErrorSpec>) -> ProductionStateV {
    let s = production_handler_node_spec_with_members(s, ProductionMembersV { refresh: None, ..s.node.members });
    let now = production_state_spec_now(s);
    let s = production_state_spec_note(s, ProductionNoteV::MembershipRefresh { ok: r is Ok });
    let s = match r {
        Ok(()) => {
            if !s.node.members.read_once {
                production_handler_timers_spec_timers_start(production_handler_node_spec_with_members(s, ProductionMembersV { read_once: true, ..s.node.members }), now)
            } else {
                s
            }
        },
        Err(e) => production_state_spec_note(s, ProductionNoteV::RefreshFailed { error: production_types_spec_error_text(e) }),
    };
    let s = production_handler_node_spec_with_members(s, ProductionMembersV { next_heartbeat: Some(now.saturating_add(s.node.members.heartbeat_ms)), ..s.node.members });
    if s.loops {
        production_handler_timers_spec_timers_run(s, now)
    } else {
        s
    }
}

#[verifier::opaque]
pub open spec fn production_handler_spec_on_event(s: ProductionStateV, event: ProductionEventV) -> (ProductionStateV, Seq<ProductionEffectV>) {
    let clock = match event {
        ProductionEventV::Request { clock, .. }
        | ProductionEventV::Store { clock, .. }
        | ProductionEventV::Wake { clock, .. } => clock,
    };
    let s = ProductionStateV { clock, timers: ProductionTimersV { budget: TIMER_WORK_BUDGET, ..s.timers }, ..s };
    let s = if s.node.members.next_heartbeat is None
        && !s.node.members.refreshing()
    {
        production_handler_node_spec_members_tick(s, production_state_spec_now(s))
    } else {
        s
    };
    let s = match event {
        ProductionEventV::Request { clock, request } => match request {
            ProductionRequestEventV::Protocol(call) => production_handler_spec_request(s, call),
            ProductionRequestEventV::Debug(call) => production_debug_spec_debug_begin(s, call),
        },
        ProductionEventV::Store { op, response, .. } => {
            let owner = if s.ops.contains_key(op) { Some(s.ops[op]) } else { None };
            let s = ProductionStateV { ops: s.ops.remove(op), ..s };
            match owner {
                Some(ProductionOwner::Flight(f)) => production_handler_docs_spec_flight_completed(s, f, op, response),
                Some(ProductionOwner::Members) => production_handler_node_spec_members_completed(s, op, response),
                Some(ProductionOwner::Timers) => production_handler_timers_spec_timers_completed(s, op, response),
                Some(ProductionOwner::Debug) => production_debug_spec_debug_completed(s, op, response),
                _ => s,
            }
        },
        ProductionEventV::Wake { armed, .. } => {
            let s = ProductionStateV { last_wake: None, ..s };
            if s.loops {
                let now = production_state_spec_now(s);
                match armed {
                    ProductionArmed::Heartbeat => production_handler_timers_spec_timers_run(production_handler_node_spec_members_tick(s, now), now),
                    ProductionArmed::Wheel => production_handler_node_spec_members_tick(production_handler_timers_spec_timers_run(s, now), now),
                }
            } else {
                s
            }
        },
    };
    let s = production_handler_spec_schedule_wake(s);
    (ProductionStateV { out: Seq::empty(), ..s }, s.out)
}

#[verifier::opaque]
pub open spec fn production_handler_spec_request(s: ProductionStateV, call: ProductionCallV) -> ProductionStateV {
    let now = if call.pinned || call.now > s.node.fleet_at { call.now } else { s.node.fleet_at };
    let stage = match call.then {
        Some((then, check)) => ProductionStageV::Detached { then, check: Some(check) },
        None => ProductionStageV::Whole,
    };
    let work = ProductionWorkV::Request { id: call.id, kind: call.kind, corr: call.corr, req: call.request, action_kind: call.action_kind, now, stage };
    production_handler_docs_spec_submit(s, call.target, work, None, false)
}

#[verifier::opaque]
pub open spec fn production_handler_spec_schedule_wake(s: ProductionStateV) -> ProductionStateV {
    if !s.loops {
        s
    } else {
        let now = production_state_spec_now(s);
        let heartbeat = match s.node.members.wake_at() {
            Some(at) => Some((at, ProductionArmed::Heartbeat)),
            None => None,
        };
        let timers = production_state_timers_spec_next_wake(s.timers, now);
        let next = match (heartbeat, timers) {
            (Some((ha, hb)), Some((ta, tb))) => Some(if ha < ta { (ha, hb) } else { (ta, tb) }),
            (Some(h), None) => Some(h),
            (None, Some(t)) => Some(t),
            (None, None) => None,
        };
        let (s, moved) = production_state_spec_wake_moved(s, next);
        if moved {
            match next {
                Some((at, armed)) => {
                    let after = at.saturating_sub(now);
                    production_state_spec_emit(s, ProductionEffectV::Wake { after_ms: if after > 1 { after } else { 1 }, armed })
                },
                None => s,
            }
        } else {
            s
        }
    }
}

pub open spec fn production_debug_spec_debug_new() -> ProductionDebugV {
    ProductionDebugV { current: None, queue: Seq::empty() }
}

pub open spec fn production_debug_spec_with_debug(s: ProductionStateV, d: ProductionDebugV) -> ProductionStateV {
    ProductionStateV { debug: d, ..s }
}

pub open spec fn production_debug_spec_current(s: ProductionStateV, op: Option<ProductionDebugOpV>) -> ProductionStateV {
    production_debug_spec_with_debug(s, ProductionDebugV { current: op, ..s.debug })
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_begin(s: ProductionStateV, call: ProductionDebugCallV) -> ProductionStateV {
    if s.debug.current is Some {
        production_debug_spec_with_debug(s, ProductionDebugV { queue: s.debug.queue.push(call), ..s.debug })
    } else {
        production_debug_spec_debug_start(s, call)
    }
}

#[verifier::opaque]
pub open spec fn production_debug_spec_list_docs(s: ProductionStateV) -> (ProductionStateV, Map<u64, bool>) {
    let (s, op1) = production_state_spec_store(s, StoreReqSpec::List { prefix: s.keys.prefix + "wf/"@, max_keys: usize::MAX }, ProductionOwner::Debug);
    let (s, op2) = production_state_spec_store(s, StoreReqSpec::List { prefix: s.keys.prefix + "sched/"@, max_keys: usize::MAX }, ProductionOwner::Debug);
    (s, Map::<u64, bool>::empty().insert(op1, true).insert(op2, true))
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_start(s: ProductionStateV, call: ProductionDebugCallV) -> ProductionStateV {
    match call {
        ProductionDebugCallV::Reset { id, kind, corr } => {
            let (s, op) = production_state_spec_store(s, StoreReqSpec::List { prefix: s.cfg.prefix, max_keys: usize::MAX }, ProductionOwner::Debug);
            production_debug_spec_current(s, Some(ProductionDebugOpV::Reset { id, kind, corr, phase: ProductionDebugResetV::Listing { op } }))
        },
        ProductionDebugCallV::Snap { id, kind, corr } => {
            let (s, ops) = production_debug_spec_list_docs(s);
            production_debug_spec_current(s, Some(ProductionDebugOpV::Snap { id, kind, corr, phase: ProductionDebugSnapV::Gathering { ops, pending: Map::empty(), origins: Seq::empty(), schedules: Seq::empty() } }))
        },
        ProductionDebugCallV::Tick { id, kind, corr, time } => {
            let (s, ops) = production_debug_spec_list_docs(s);
            production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase: ProductionDebugTickV::Listing { ops, origins: Seq::empty(), schedules: Seq::empty() } }))
        },
    }
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_reply(s: ProductionStateV, id: u64, kind: Seq<char>, corr: Seq<char>, status: u16, body: ProductionDebugBodyV) -> ProductionStateV {
    let s = production_state_spec_emit(s, ProductionEffectV::Reply { id, response: Ok(ProductionAnswerV::Debug { kind, corr, status, body }) });
    if s.debug.queue.len() > 0 {
        let call = s.debug.queue[0];
        production_debug_spec_debug_start(production_debug_spec_with_debug(s, ProductionDebugV { queue: s.debug.queue.drop_first(), ..s.debug }), call)
    } else {
        s
    }
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_fail(s: ProductionStateV, id: u64, kind: Seq<char>, corr: Seq<char>, e: StoreErrorSpec) -> ProductionStateV {
    let s = production_debug_spec_current(s, None);
    production_debug_spec_debug_reply(s, id, kind, corr, 503, ProductionDebugBodyV::Message(production_types_spec_error_text(e)))
}

pub open spec fn production_debug_spec_resettable(class: Option<Seq<char>>) -> bool {
    match class {
        Some(c) => c == "wf"@ || c == "sched"@ || c == "t"@,
        None => false,
    }
}

pub open spec fn production_debug_spec_delete_keys(s: ProductionStateV, keys: Seq<Seq<char>>, pending: Map<u64, bool>) -> (ProductionStateV, Map<u64, bool>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (s, pending)
    } else {
        let key = keys[0];
        let (s, pending) = if production_debug_spec_resettable(production_keys_spec_class_of(s.keys.prefix, key)) {
            let (s, op) = production_state_spec_store(s, StoreReqSpec::Del { key }, ProductionOwner::Debug);
            (s, pending.insert(op, true))
        } else {
            (s, pending)
        };
        production_debug_spec_delete_keys(s, keys.drop_first(), pending)
    }
}

pub open spec fn production_debug_spec_get_keys(s: ProductionStateV, keys: Seq<Seq<char>>, pending: Map<u64, bool>) -> (ProductionStateV, Map<u64, bool>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (s, pending)
    } else {
        let key = keys[0];
        let schedule = production_keys_spec_class_of(s.keys.prefix, key) == Some("sched"@);
        let (s, op) = production_state_spec_store(s, StoreReqSpec::Get { key }, ProductionOwner::Debug);
        production_debug_spec_get_keys(s, keys.drop_first(), pending.insert(op, schedule))
    }
}

pub open spec fn production_debug_spec_tick_names(prefix: Seq<char>, keys: Seq<Seq<char>>, origins: Seq<Seq<char>>, schedules: Seq<Seq<char>>) -> (Seq<Seq<char>>, Seq<Seq<char>>)
    decreases keys.len(),
{
    if keys.len() == 0 {
        (origins, schedules)
    } else {
        let key = keys[0];
        let class = production_keys_spec_class_of(prefix, key);
        let name = production_keys_spec_decode_key(production_keys_spec_last_segment(key));
        let (origins, schedules) = if class == Some("wf"@) {
            match name {
                Some(o) => (origins.push(o), schedules),
                None => (origins, schedules),
            }
        } else if class == Some("sched"@) {
            match name {
                Some(sch) => (origins, schedules.push(sch)),
                None => (origins, schedules),
            }
        } else {
            (origins, schedules)
        };
        production_debug_spec_tick_names(prefix, keys.drop_first(), origins, schedules)
    }
}

pub open spec fn production_debug_spec_submit_sweeps(s: ProductionStateV, origins: Seq<Seq<char>>, time: u64) -> ProductionStateV
    decreases origins.len(),
{
    if origins.len() == 0 {
        s
    } else {
        let s = production_handler_docs_spec_submit(s, ProductionTargetV::Origin(origins[0]), ProductionWorkV::Sweep { fired: None, now: time }, None, true);
        production_debug_spec_submit_sweeps(s, origins.drop_first(), time)
    }
}

pub open spec fn production_debug_spec_submit_fires(s: ProductionStateV, schedules: Seq<Seq<char>>, time: u64) -> ProductionStateV
    decreases schedules.len(),
{
    if schedules.len() == 0 {
        s
    } else {
        let s = production_handler_docs_spec_submit(s, ProductionTargetV::Schedule(schedules[0]), ProductionWorkV::Fire { schedule: schedules[0], fired: None, now: time }, None, true);
        production_debug_spec_submit_fires(s, schedules.drop_first(), time)
    }
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_completed(s: ProductionStateV, op: u64, outcome: StoreRes) -> ProductionStateV {
    match s.debug.current {
        None => s,
        Some(current) => {
            let expected = match current {
                ProductionDebugOpV::Reset { phase: ProductionDebugResetV::Listing { op: o }, .. } => o == op,
                ProductionDebugOpV::Snap { phase: ProductionDebugSnapV::Gathering { ops, pending, .. }, .. } => ops.contains_key(op) || pending.contains_key(op),
                ProductionDebugOpV::Reset { phase: ProductionDebugResetV::Deleting { pending }, .. } => pending.contains_key(op),
                ProductionDebugOpV::Tick { phase: ProductionDebugTickV::Listing { ops, .. }, .. } => ops.contains_key(op),
                ProductionDebugOpV::Tick { .. } => false,
            };
            if !expected {
                s
            } else {
                let s = production_debug_spec_current(s, None);
                match current {
                    ProductionDebugOpV::Reset { id, kind, corr, phase } => match (phase, outcome) {
                        (ProductionDebugResetV::Listing { .. }, StoreRes::List { result: Ok(keys) }) => {
                            let (s, pending) = production_debug_spec_delete_keys(s, keys.deep_view(), Map::empty());
                            if pending =~= Map::<u64, bool>::empty() {
                                production_debug_spec_debug_reset_done(s, id, kind, corr)
                            } else {
                                production_debug_spec_current(s, Some(ProductionDebugOpV::Reset { id, kind, corr, phase: ProductionDebugResetV::Deleting { pending } }))
                            }
                        },
                        (ProductionDebugResetV::Deleting { pending }, StoreRes::Del { result: Ok(()) }) => {
                            let pending = pending.remove(op);
                            if pending =~= Map::<u64, bool>::empty() {
                                production_debug_spec_debug_reset_done(s, id, kind, corr)
                            } else {
                                production_debug_spec_current(s, Some(ProductionDebugOpV::Reset { id, kind, corr, phase: ProductionDebugResetV::Deleting { pending } }))
                            }
                        },
                        (_, StoreRes::List { result: Err(e) } | StoreRes::Del { result: Err(e) }) =>
                            production_debug_spec_debug_fail(s, id, kind, corr, e.deep_view()),
                        _ => production_debug_spec_debug_fail(s, id, kind, corr, production_types_spec_unexpected()),
                    },
                    ProductionDebugOpV::Snap { id, kind, corr, phase: ProductionDebugSnapV::Gathering { ops, pending, origins, schedules } } => {
                        let gathered: Result<(ProductionStateV, Map<u64, bool>, Map<u64, bool>, Seq<DocumentBodyV>, Seq<ScheduleSpec>), StoreErrorSpec> = match outcome {
                            StoreRes::List { result: Ok(keys) } => {
                                let ops = ops.remove(op);
                                let (s, pending) = production_debug_spec_get_keys(s, keys.deep_view(), pending);
                                Ok((s, ops, pending, origins, schedules))
                            },
                            StoreRes::Get { result: Ok(got) } => {
                                let schedule = if pending.contains_key(op) { pending[op] } else { false };
                                let pending = pending.remove(op);
                                match got {
                                    Some((bytes, _)) => {
                                        if schedule {
                                            match production_document_spec_decode_schedule(bytes@) {
                                                Ok(loaded) => match production_document_spec_loaded_body(loaded) {
                                                    DocumentBodyV::Schedule(Some(row)) => Ok((s, ops, pending, origins, schedules.push(row.deep_view()))),
                                                    _ => Ok((s, ops, pending, origins, schedules)),
                                                },
                                                Err(e) => Err(StoreErrorSpec::Unavailable(e)),
                                            }
                                        } else {
                                            match production_document_spec_decode_workflow(bytes@) {
                                                Ok(loaded) => Ok((s, ops, pending, origins.push(production_document_spec_loaded_body(loaded)), schedules)),
                                                Err(e) => Err(StoreErrorSpec::Unavailable(e)),
                                            }
                                        }
                                    },
                                    None => Ok((s, ops, pending, origins, schedules)),
                                }
                            },
                            StoreRes::List { result: Err(e) } | StoreRes::Get { result: Err(e) } =>
                                Err(e.deep_view()),
                            _ => Err(production_types_spec_unexpected()),
                        };
                        match gathered {
                            Err(e) => production_debug_spec_debug_fail(s, id, kind, corr, e),
                            Ok((s, ops, pending, origins, schedules)) => {
                                if ops =~= Map::<u64, bool>::empty() && pending =~= Map::<u64, bool>::empty() {
                                    production_debug_spec_debug_reply(s, id, kind, corr, 200, ProductionDebugBodyV::Snap { origins, schedules })
                                } else {
                                    production_debug_spec_current(s, Some(ProductionDebugOpV::Snap { id, kind, corr, phase: ProductionDebugSnapV::Gathering { ops, pending, origins, schedules } }))
                                }
                            },
                        }
                    },
                    ProductionDebugOpV::Tick { id, kind, corr, time, phase } => match (phase, outcome) {
                        (ProductionDebugTickV::Listing { ops, origins, schedules }, StoreRes::List { result: Ok(keys) }) => {
                            let ops = ops.remove(op);
                            let (origins, schedules) = production_debug_spec_tick_names(s.keys.prefix, keys.deep_view(), origins, schedules);
                            if !(ops =~= Map::<u64, bool>::empty()) {
                                production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase: ProductionDebugTickV::Listing { ops, origins, schedules } }))
                            } else {
                                // every origin swept at `time`; the flights report back
                                let outstanding = origins.len() as usize;
                                if outstanding == 0 {
                                    production_debug_spec_debug_tick_fire(s, id, kind, corr, time, schedules)
                                } else {
                                    let s = production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase: ProductionDebugTickV::Sweeping { outstanding, schedules } }));
                                    production_debug_spec_submit_sweeps(s, origins, time)
                                }
                            }
                        },
                        (_, StoreRes::List { result: Err(e) }) =>
                            production_debug_spec_debug_fail(s, id, kind, corr, e.deep_view()),
                        _ => production_debug_spec_debug_fail(s, id, kind, corr, production_types_spec_unexpected()),
                    },
                }
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_reset_done(s: ProductionStateV, id: u64, kind: Seq<char>, corr: Seq<char>) -> ProductionStateV {
    let old_core = s.node.core;
    let fresh = ANode {
        id: s.cfg.node_id, ttl: s.cfg.node_ttl_ms as nat, read_any: false, epoch: 0,
        members: Seq::empty(), last_read: 0, cache: Map::empty(), armed: Map::empty(),
    };
    let core = if old_core.read_any { spec_production_read_config(fresh, old_core.last_read, old_core.epoch, old_core.members) } else { fresh };
    let s = ProductionStateV {
        cache: spec_production_cache_new(s.cfg.cache_entries, s.cfg.cache_bytes),
        node: ProductionNodeStateV { core, ..s.node },
        timers: ProductionTimersV {
            wheel: ProductionTimerWheelV { armed: Set::empty() },
            listing: None,
            backlog: Seq::empty(),
            loaded_through: None,
            closed_through: None,
            rediscover_at: None,
            backoff_until: None,
            reload_pending: s.timers.started,
            ..s.timers
        },
        ..s
    };
    production_debug_spec_debug_reply(s, id, kind, corr, 200, ProductionDebugBodyV::Object)
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_flight_done(s: ProductionStateV, work: ProductionWorkV, idle: bool) -> ProductionStateV {
    let fired_schedule = match work {
        ProductionWorkV::Fire { schedule, .. } => if !idle { Some(schedule) } else { None },
        _ => None,
    };
    production_debug_spec_debug_tick_advance(s, fired_schedule)
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_tick_fire(s: ProductionStateV, id: u64, kind: Seq<char>, corr: Seq<char>, time: u64, schedules: Seq<Seq<char>>) -> ProductionStateV {
    let outstanding = schedules.len() as usize;
    if outstanding == 0 {
        production_debug_spec_debug_reply(production_debug_spec_current(s, None), id, kind, corr, 200, ProductionDebugBodyV::List)
    } else {
        let s = production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase: ProductionDebugTickV::Firing { outstanding } }));
        production_debug_spec_submit_fires(s, schedules, time)
    }
}

#[verifier::opaque]
pub open spec fn production_debug_spec_debug_tick_advance(s: ProductionStateV, refire: Option<Seq<char>>) -> ProductionStateV {
    match s.debug.current {
        Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase }) => {
            let s = production_debug_spec_current(s, None);
            match phase {
                ProductionDebugTickV::Sweeping { outstanding, schedules } => {
                    let outstanding = outstanding.saturating_sub(if refire is None && outstanding > 0 { 1 } else { 0 });
                    if outstanding > 0 {
                        production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase: ProductionDebugTickV::Sweeping { outstanding, schedules } }))
                    } else {
                        production_debug_spec_debug_tick_fire(s, id, kind, corr, time, schedules)
                    }
                },
                ProductionDebugTickV::Firing { outstanding } => match refire {
                    Some(sch) => {
                        let s = production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase: ProductionDebugTickV::Firing { outstanding } }));
                        production_handler_docs_spec_submit(s, ProductionTargetV::Schedule(sch), ProductionWorkV::Fire { schedule: sch, fired: None, now: time }, None, true)
                    },
                    None => {
                        let outstanding = outstanding.saturating_sub(1);
                        if outstanding > 0 {
                            production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase: ProductionDebugTickV::Firing { outstanding } }))
                        } else {
                            production_debug_spec_debug_reply(s, id, kind, corr, 200, ProductionDebugBodyV::List)
                        }
                    },
                },
                ProductionDebugTickV::Listing { .. } => production_debug_spec_current(s, Some(ProductionDebugOpV::Tick { id, kind, corr, time, phase })),
            }
        },
        _ => production_debug_spec_current(s, None),
    }
}

pub uninterp spec fn production_keys_spec_encode_key(s: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_decode_key(s: Seq<char>) -> Option<Seq<char>>;

pub uninterp spec fn production_keys_spec_normalize_prefix(s: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_class_of(prefix: Seq<char>, key: Seq<char>) -> Option<Seq<char>>;

pub uninterp spec fn production_keys_spec_doc_key(prefix: Seq<char>, origin: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_sched_key(prefix: Seq<char>, id: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_members_key(prefix: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_node_prefix(prefix: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_node_key(prefix: Seq<char>, id: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_node_of_key(prefix: Seq<char>, key: Seq<char>) -> Option<Seq<char>>;

pub uninterp spec fn production_keys_spec_timer_prefix(prefix: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_bucket_prefix(prefix: Seq<char>, bucket: u64) -> Seq<char>;

pub uninterp spec fn production_keys_spec_parse_bucket_prefix(prefix: Seq<char>, p: Seq<char>) -> Option<u64>;

pub uninterp spec fn production_keys_spec_timer_key(prefix: Seq<char>, bucket_ms: u64, origin: Seq<char>, at: u64, token: u64, by: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_sched_timer_key(prefix: Seq<char>, bucket_ms: u64, id: Seq<char>, at: u64, token: u64, by: Seq<char>) -> Seq<char>;

pub uninterp spec fn production_keys_spec_parse_timer_key(key: Seq<char>) -> Option<ProductionTimerEntryV>;

pub uninterp spec fn production_keys_spec_last_segment(key: Seq<char>) -> Seq<char>;

pub open spec fn production_keys_spec_bucket_of(at: u64, bucket_ms: u64) -> u64 {
    let width = if bucket_ms < 1 { 1u64 } else { bucket_ms };
    ((at / width) * width) as u64
}

pub open spec fn production_document_spec_loaded_body(loaded: LoadedDocumentV) -> DocumentBodyV {
    spec_stored_body(loaded.document)
}

pub open spec fn production_document_spec_loaded_version(loaded: LoadedDocumentV) -> u64 {
    spec_stored_version(loaded.document)
}

pub open spec fn production_document_spec_loaded_committed_at(loaded: LoadedDocumentV) -> u64 {
    spec_stored_committed_at(loaded.document)
}

pub open spec fn production_document_spec_empty_workflow(document: Seq<char>) -> LoadedDocumentV {
    LoadedDocumentV {
        document: spec_empty_stored_workflow(document),
        change_count: 0,
        bytes: 0,
    }
}

pub open spec fn production_document_spec_empty_schedule(document: Seq<char>) -> LoadedDocumentV {
    LoadedDocumentV {
        document: spec_empty_stored_schedule(document),
        change_count: 0,
        bytes: 0,
    }
}

pub open spec fn production_document_spec_clamp_now(committed_at: u64, now: u64) -> u64 {
    if committed_at > now { committed_at } else { now }
}

pub open spec fn production_document_spec_removed_any(before: DocumentBodyV, after: DocumentBodyV) -> bool {
    match (before, after) {
        (DocumentBodyV::Workflow(b), DocumentBodyV::Workflow(a)) => !b.dom().subset_of(a.dom()),
        (DocumentBodyV::Schedule(Some(_)), DocumentBodyV::Schedule(None)) => true,
        (DocumentBodyV::Schedule(_), DocumentBodyV::Schedule(_)) => false,
        _ => true,
    }
}

pub uninterp spec fn production_document_spec_decode_workflow(bytes: Seq<u8>) -> Result<LoadedDocumentV, Seq<char>>;

pub uninterp spec fn production_document_spec_decode_schedule(bytes: Seq<u8>) -> Result<LoadedDocumentV, Seq<char>>;

pub uninterp spec fn production_document_spec_encode_body(document: StoredDocumentV) -> Seq<u8>;

pub uninterp spec fn production_document_spec_encode_delta(
    before: StoredDocumentV,
    after: StoredDocumentV,
) -> (Seq<u8>, usize);

pub open spec fn production_reason_spec_reason(status: u16) -> Seq<char> {
    if status == 400 { "Bad request"@ }
    else if status == 403 { "Forbidden"@ }
    else if status == 404 { "Not found"@ }
    else if status == 409 { "Conflict"@ }
    else if status == 422 { "Unprocessable"@ }
    else { "Error"@ }
}

pub open spec fn production_reason_spec_status_of(r: AResponse) -> u16 {
    match r {
        AResponse::Promise(p) => p.status,
        AResponse::Schedule(c) => c.status,
        AResponse::Status(st) => st.status,
        AResponse::TaskGet(g) => g.status,
        AResponse::TaskClaim(c) => c.status,
        AResponse::TaskFence(f) => f.status,
    }
}

pub open spec fn production_reason_spec_target_of(tags: Seq<(String, String)>) -> Option<Seq<char>>
    decreases tags.len(),
{
    if tags.len() == 0 {
        None
    } else if tags[0].0@ == "resonate:target"@ {
        Some(tags[0].1@)
    } else {
        production_reason_spec_target_of(tags.drop_first())
    }
}

pub open spec fn production_reason_spec_object(doc: DocumentBodyV, id: Seq<char>) -> Option<ObjV> {
    if spec_workflow_map(doc).contains_key(id) { Some(spec_workflow_map(doc)[id]) } else { None }
}

pub open spec fn production_reason_spec_any_missing(doc: DocumentBodyV, actions: Seq<echod_types::PromiseRegisterCallbackReq>) -> bool
    decreases actions.len(),
{
    if actions.len() == 0 {
        false
    } else if production_reason_spec_object(doc, actions[0].awaited@) is None {
        true
    } else {
        production_reason_spec_any_missing(doc, actions.drop_first())
    }
}

pub open spec fn production_reason_spec_reason_for(kind: Seq<char>, req: Request, status: u16, doc: DocumentBodyV) -> Seq<char> {
    if (kind == "promise.get"@ || kind == "promise.settle"@) && status == 404 {
        "Promise not found"@
    } else if (kind == "promise.register_callback"@ || kind == "promise.register_listener"@) && status == 404 {
        "Awaited promise not found"@
    } else if kind == "promise.register_callback"@ && status == 422 {
        match req {
            Request::PromiseRegisterCallback(c) => match production_reason_spec_object(doc, c.awaiter@) {
                None => "Awaiter promise not found"@,
                Some(w) => if production_reason_spec_target_of(w.promise.tags@) is None { "Awaiter promise has no resonate:target tag"@ } else { "Awaited promise is not awaitable"@ },
            },
            _ => "Awaited promise is not awaitable"@,
        }
    } else if kind == "promise.register_listener"@ && status == 422 {
        "Awaited promise is not awaitable"@
    } else if (kind == "task.get"@ || kind == "task.acquire"@ || kind == "task.release"@ || kind == "task.fulfill"@ || kind == "task.suspend"@ || kind == "task.fence"@ || kind == "task.halt"@ || kind == "task.continue"@) && status == 404 {
        "Task not found"@
    } else if kind == "task.create"@ && status == 409 {
        "Already exists"@
    } else if kind == "task.create"@ && status == 422 {
        "The promise does not have a resonate:target tag"@
    } else if kind == "task.acquire"@ && status == 409 {
        match req {
            Request::TaskAcquire(a) => match production_reason_spec_object(doc, a.id@) {
                Some(o) => match o.task {
                    Some(t) => if t.state == TaskState::Pending { "Version mismatch"@ } else { "Task is not pending"@ },
                    None => "Task is not pending"@,
                },
                None => "Task is not pending"@,
            },
            _ => "Task is not pending"@,
        }
    } else if (kind == "task.release"@ || kind == "task.fulfill"@) && status == 409 {
        "Task version mismatch or invalid state"@
    } else if kind == "task.suspend"@ && status == 409 {
        "Task is not acquired or version mismatch"@
    } else if kind == "task.suspend"@ && status == 422 {
        match req {
            Request::TaskSuspend(q) => if production_reason_spec_any_missing(doc, q.actions@) { "Awaited promise not found"@ } else { "Awaited promise is not awaitable"@ },
            _ => "Awaited promise is not awaitable"@,
        }
    } else if kind == "task.fence"@ && status == 409 {
        "Version mismatch"@
    } else if kind == "task.halt"@ && status == 409 {
        "Task is fulfilled"@
    } else if kind == "task.continue"@ && status == 409 {
        "Task is not halted"@
    } else if (kind == "schedule.get"@ || kind == "schedule.delete"@) && status == 404 {
        "Schedule not found"@
    } else {
        production_reason_spec_reason(status)
    }
}

pub open spec fn production_target_spec_name(t: ProductionTargetV) -> Seq<char> {
    match t {
        ProductionTargetV::Origin(o) => o,
        ProductionTargetV::Schedule(id) => "sched:"@ + id,
    }
}

pub open spec fn production_target_spec_of_name(name: Seq<char>) -> ProductionTargetV {
    if name.len() >= 6 && name.subrange(0, 6) == "sched:"@ {
        ProductionTargetV::Schedule(name.subrange(6, name.len() as int))
    } else {
        ProductionTargetV::Origin(name)
    }
}

pub open spec fn production_types_spec_error_text(e: StoreErrorSpec) -> Seq<char> {
    match e {
        StoreErrorSpec::PreconditionFailed => "precondition failed"@,
        StoreErrorSpec::Unavailable(m) => "store unavailable: "@ + m,
    }
}

pub open spec fn production_types_spec_unexpected() -> StoreErrorSpec {
    StoreErrorSpec::Unavailable("the store answered something else"@)
}

pub open spec fn production_verified_text_spec_starts_with(s: Seq<char>, p: Seq<char>) -> bool {
    s.len() >= p.len() && s.subrange(0, p.len() as int) == p
}

#[cfg(verus_keep_ghost)]
impl ProductionRefreshV {
    pub open spec fn expects(self, op: u64) -> bool {
        match self {
            ProductionRefreshV::Announcing { op: o, .. } | ProductionRefreshV::Listing { op: o, .. } | ProductionRefreshV::Config { op: o, .. } | ProductionRefreshV::Writing { op: o, .. } => o == op,
            ProductionRefreshV::Reading { pending, .. } => pending.contains_key(op),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl ProductionMembersV {
    pub open spec fn refreshing(self) -> bool {
        self.refresh is Some
    }

    pub open spec fn wake_at(self) -> Option<u64> {
        if self.refreshing() { None } else { self.next_heartbeat }
    }
}

#[cfg(verus_keep_ghost)]
impl ProductionListingV {
    pub open spec fn ready(self) -> bool {
        matches!(self, Self::Scan { .. } | Self::Applying { .. } | Self::Retry { .. })
    }

    pub open spec fn expects(self, op: u64) -> bool {
        match self {
            ProductionListingV::Prefixes { op: o, .. } | ProductionListingV::Bucket { op: o, .. } | ProductionListingV::Extend { op: o, .. } | ProductionListingV::Relist { op: o, .. } => o == op,
            _ => false,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl ProductionWorkV {
    pub open spec fn now(self) -> u64 {
        match self {
            ProductionWorkV::Request { now, .. } | ProductionWorkV::Sweep { now, .. } | ProductionWorkV::Fire { now, .. } => now,
        }
    }

    pub open spec fn is_sweep(self) -> bool {
        self is Sweep
    }
}

#[cfg(verus_keep_ghost)]
impl ProductionCommittingV {
    /// The store call the commit waits on.
    pub open spec fn expects(self) -> Option<u64> {
        match self.issued {
            Some(ProductionIssuedV::Key { op, .. }) | Some(ProductionIssuedV::Write { op, .. }) => Some(op),
            None => None,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl ProductionPhaseV {
    /// The store call the flight waits on.
    pub open spec fn expects(self) -> Option<u64> {
        match self {
            ProductionPhaseV::Idle | ProductionPhaseV::FireWaitingOrigin(_) => None,
            ProductionPhaseV::Loading { op, .. } | ProductionPhaseV::FireLoadingSchedule { op } | ProductionPhaseV::FireLoadingOrigin { op, .. } => Some(op),
            ProductionPhaseV::Origin { commit, .. } | ProductionPhaseV::FireOrigin { commit, .. } => commit.expects(),
            ProductionPhaseV::Schedule { commit, .. } | ProductionPhaseV::FireIdle { commit } | ProductionPhaseV::FireSchedule { commit } => commit.expects(),
        }
    }
}


#[cfg(verus_keep_ghost)]
impl ProductionTimerEntryV {
    pub open spec fn deadline(self) -> u64 {
        match self {
            ProductionTimerEntryV::Origin { deadline, .. } | ProductionTimerEntryV::Schedule { deadline, .. } => deadline,
        }
    }

    pub open spec fn target(self) -> Seq<char> {
        match self {
            ProductionTimerEntryV::Origin { origin, .. } => origin,
            ProductionTimerEntryV::Schedule { id, .. } => id,
        }
    }

    pub open spec fn token(self) -> u64 {
        match self {
            ProductionTimerEntryV::Origin { token, .. } | ProductionTimerEntryV::Schedule { token, .. } => token,
        }
    }

    pub open spec fn by(self) -> Seq<char> {
        match self {
            ProductionTimerEntryV::Origin { by, .. } | ProductionTimerEntryV::Schedule { by, .. } => by,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl ProductionCachedV {
    /// What the entry weighs against the byte budget: the object's size.
    pub open spec fn weight(self) -> u64 {
        if self.loaded.bytes < 1 { 1u64 } else { self.loaded.bytes }
    }
}
pub open spec fn spec_production_cache_find(entries: Seq<ProductionCacheEntryV>, origin: Seq<char>) -> Option<int>
    decreases entries.len(),
{
    if entries.len() == 0 {
        None
    } else if entries[0].origin == origin {
        Some(0int)
    } else {
        match spec_production_cache_find(entries.drop_first(), origin) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

pub open spec fn spec_production_cache_new(max_entries: usize, max_bytes: u64) -> ProductionCacheV {
    ProductionCacheV {
        entries: Seq::empty(),
        bytes: 0,
        max_entries: if max_entries < 1 { 1usize } else { max_entries },
        max_bytes: if max_bytes < 1 { 1u64 } else { max_bytes },
        hits: 0,
        misses: 0,
        evictions: 0,
    }
}

/// A hit moves the entry to the end and counts; a miss counts.
pub open spec fn spec_production_cache_get(c: ProductionCacheV, origin: Seq<char>) -> (ProductionCacheV, Option<ProductionCachedV>) {
    match spec_production_cache_find(c.entries, origin) {
        Some(i) => {
            let e = c.entries[i];
            (ProductionCacheV { entries: c.entries.remove(i).push(e), hits: c.hits.wrapping_add(1), ..c }, Some(e.cached))
        },
        None => (ProductionCacheV { misses: c.misses.wrapping_add(1), ..c }, None),
    }
}

/// The entry of `origin` taken out, its weight returned to the budget.
pub open spec fn spec_production_cache_remove(c: ProductionCacheV, origin: Seq<char>) -> ProductionCacheV {
    match spec_production_cache_find(c.entries, origin) {
        Some(i) => ProductionCacheV {
            entries: c.entries.remove(i),
            bytes: c.bytes.wrapping_sub(c.entries[i].cached.weight()),
            ..c
        },
        None => c,
    }
}

/// Evict, least recent first, until the bounds hold, keeping `keep`: the
/// entries evicted, in order, and the cache after.
pub open spec fn spec_production_cache_trim(c: ProductionCacheV, keep: Seq<char>) -> (Seq<Seq<char>>, ProductionCacheV)
    decreases c.entries.len(),
{
    if (c.entries.len() > c.max_entries || c.bytes > c.max_bytes) && c.entries.len() > 0 && c.entries[0].origin != keep {
        let e = c.entries[0];
        let next = ProductionCacheV {
            entries: c.entries.drop_first(),
            bytes: c.bytes.wrapping_sub(e.cached.weight()),
            evictions: c.evictions.wrapping_add(1),
            ..c
        };
        let (rest, after) = spec_production_cache_trim(next, keep);
        (seq![e.origin] + rest, after)
    } else {
        (Seq::empty(), c)
    }
}

/// Remember `cached` for `origin` in place of what was there, as the most
/// recent entry; then trim. The entry just put is never evicted, however
/// heavy: the request that committed it reads it next.
pub open spec fn spec_production_cache_put(c: ProductionCacheV, origin: Seq<char>, cached: ProductionCachedV) -> (Seq<Seq<char>>, ProductionCacheV) {
    let c = spec_production_cache_remove(c, origin);
    let c = ProductionCacheV {
        entries: c.entries.push(ProductionCacheEntryV { origin, cached }),
        bytes: c.bytes.wrapping_add(cached.weight()),
        ..c
    };
    spec_production_cache_trim(c, origin)
}

pub open spec fn spec_production_cache_stats(c: ProductionCacheV) -> ProductionCacheStatsV {
    ProductionCacheStatsV { entries: c.entries.len() as usize, bytes: c.bytes, hits: c.hits, misses: c.misses, evictions: c.evictions }
}

// ---------------------------------------------------------------------------
// The cache, step for step
// ---------------------------------------------------------------------------


pub open spec fn spec_production_step(job: AJob, doc: DocumentBodyV, now: u64, retry_timeout: u64, limit: nat) -> (DocumentBodyV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
    match job {
        AJob::Request(request) => {
            let (next, response, born, notes) =
                spec_request_transition(doc, request, now, retry_timeout, limit);
            (next, Some(response), born, notes)
        },
        AJob::Sweep => {
            let (next, born, notes) = spec_sweep(doc, now, retry_timeout, limit);
            (next, None, born, notes)
        },
        AJob::Fire => spec_run_due(doc, now, retry_timeout),
        AJob::Occurrence(pending) => (spec_occurrence(doc, pending, now), None, Seq::empty(), Seq::empty()),
    }
}

/// The model's job as this flight's: one due step is `Fire`.

pub open spec fn production_job_of(job: JobV) -> AJob {
    match job {
        JobV::External(request) => AJob::Request(request),
        JobV::Due => AJob::Fire,
        JobV::Occurrence(pending) => AJob::Occurrence(pending),
    }
}

/// For model-native due and occurrence jobs, `spec_decide` writes the
/// document `spec_production_step` leaves. Request jobs use the stronger process-level
/// pre-sweep/handler transition and are verified directly by
/// [`super::flight::decide`], rather than by Rover's raw-handler step.

pub open spec fn production_answer_v(step: AStep, o: Option<StoreRes>) -> AAnswer {
    match (step, o) {
        (_, None) => AAnswer::Fresh,
        (AStep::PuttingKey(_), Some(StoreRes::Put { result: Ok(()) }))
        | (AStep::DeletingPrevious(_), Some(StoreRes::Del { result: Ok(()) }))
        | (AStep::DeletingFired(_), Some(StoreRes::Del { result: Ok(()) })) => AAnswer::Done,
        (AStep::Writing { .. }, Some(StoreRes::PutIfMatch { result: Ok(tag) }))
        | (AStep::Writing { .. }, Some(StoreRes::PutIfNoneMatch { result: Ok(tag) }))
        | (AStep::Writing { .. }, Some(StoreRes::AppIfMatch { result: Ok(tag) })) => AAnswer::Written(tag.0@),
        (AStep::PuttingKey(_), Some(StoreRes::Put { result: Err(e) }))
        | (AStep::DeletingPrevious(_), Some(StoreRes::Del { result: Err(e) }))
        | (AStep::DeletingFired(_), Some(StoreRes::Del { result: Err(e) }))
        | (AStep::Writing { .. }, Some(StoreRes::PutIfMatch { result: Err(e) }))
        | (AStep::Writing { .. }, Some(StoreRes::PutIfNoneMatch { result: Err(e) }))
        | (AStep::Writing { .. }, Some(StoreRes::AppIfMatch { result: Err(e) })) => AAnswer::Failed(e),
        (_, Some(_)) => AAnswer::Other,
    }
}

/// A commit before its first call: the verified plan for it.

pub open spec fn spec_production_new(n: ANode, origin: Seq<char>, etag: Option<Seq<char>>, deadline: Option<nat>, changed: bool, fired: Option<AFired>, token: nat) -> ASequence {
    let fired_key = match fired { Some(f) => Some(f.key), None => None };
    ASequence {
        origin,
        etag,
        changed,
        fired,
        token,
        plan: spec_production_prepare(n, origin, etag, deadline, changed, fired_key),
        step: AStep::Start,
    }
}

/// After the write: the key fired is collected, behind it.

pub open spec fn spec_production_collect(s: ASequence, n: ANode) -> (ASequence, ANode, AOutcome) {
    match s.fired {
        Some(f) => (
            ASequence { step: AStep::DeletingFired(f.key), ..s },
            spec_production_collected(n, s.origin, f.key),
            AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }),
        ),
        None => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: false })),
    }
}

/// One decision of the commit: given the answer to the call it waited on,
/// the next call, or the end.
///
/// (1) The key for the new deadline, before the state that arms it.
/// (2) The document. A document that did not change under a fired key is
///     rewritten at a new version, so that no commit in flight that armed
///     the key can land on the version it loaded.
/// (3) The key replaced, or no longer needed; best effort.
/// (4) The key kept, remembered with the version written.
/// (5) The key fired: the write that just landed fences every commit that
///     armed it and has not written yet.

pub open spec fn spec_production_advance(s: ASequence, n: ANode, answer: AAnswer) -> (ASequence, ANode, AOutcome) {
    match s.step {
        AStep::Start => {
            if s.changed {
                match s.plan.deadline {
                    Some(at) if s.plan.rearm => {
                        let key = AKey { origin: s.origin, at, token: s.token };
                        (ASequence { step: AStep::PuttingKey(key), ..s }, n, AOutcome::Act(AAct::PutKey(key)))
                    },
                    _ => (ASequence { step: AStep::Writing { idle: false }, ..s }, n, AOutcome::Act(AAct::Write { cond: s.etag, idle: false })),
                }
            } else if s.fired is Some {
                (ASequence { step: AStep::Writing { idle: true }, ..s }, n, AOutcome::Act(AAct::Write { cond: s.etag, idle: true }))
            } else {
                (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: false }))
            }
        },
        AStep::PuttingKey(key) => match answer {
            AAnswer::Done => (
                ASequence { step: AStep::Writing { idle: false }, plan: spec_production_armed(s.plan, key), ..s },
                n,
                AOutcome::Act(AAct::Write { cond: s.etag, idle: false }),
            ),
            AAnswer::Failed(e) => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(Some(e))),
            _ => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(None)),
        },
        AStep::Writing { idle } => match answer {
            AAnswer::Written(tag) => {
                let s = ASequence { etag: Some(tag), ..s };
                if idle {
                    spec_production_collect(s, n)
                } else {
                    match spec_production_to_disarm(s.plan) {
                        Some(previous) => (
                            ASequence { step: AStep::DeletingPrevious(previous), ..s },
                            n,
                            AOutcome::Act(AAct::DeleteKey { key: previous, by: n.id }),
                        ),
                        None => spec_production_collect(s, spec_production_finish(n, s.plan, tag)),
                    }
                }
            },
            AAnswer::Failed(e) => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(Some(e))),
            _ => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(None)),
        },
        AStep::DeletingPrevious(_) => {
            let tag = match s.etag { Some(t) => t, None => Seq::empty() };
            spec_production_collect(s, spec_production_finish(n, s.plan, tag))
        },
        AStep::DeletingFired(_) => match answer {
            AAnswer::Done => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: true })),
            _ => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: false })),
        },
        AStep::Over => (s, n, AOutcome::Act(AAct::Done { deleted: false })),
    }
}

// ---------------------------------------------------------------------------
// The sequence as a whole
// ---------------------------------------------------------------------------

/// The answer a store that serves every call gives to the call a step waits on.

pub open spec fn spec_production_served(s: ASequence, tag: Seq<char>) -> AAnswer {
    match s.step {
        AStep::Start => AAnswer::Fresh,
        AStep::Writing { .. } => AAnswer::Written(tag),
        _ => AAnswer::Done,
    }
}

/// The acts of a commit against a store that serves every call, up to `k` decisions.

pub open spec fn spec_production_run(s: ASequence, n: ANode, tag: Seq<char>, k: nat) -> (Seq<AAct>, ASequence, ANode)
    decreases k,
{
    if k == 0 || s.step is Over {
        (Seq::empty(), s, n)
    } else {
        match spec_production_advance(s, n, spec_production_served(s, tag)) {
            (s2, n2, AOutcome::Act(act)) => {
                let (acts, s3, n3) = spec_production_run(s2, n2, tag, (k - 1) as nat);
                (seq![act] + acts, s3, n3)
            },
            (s2, n2, AOutcome::Failed(_)) => (Seq::empty(), s2, n2),
        }
    }
}

/// The key a commit arms, if it arms one.

pub open spec fn spec_production_arms(s: ASequence) -> Option<AKey> {
    match s.plan.deadline {
        Some(at) if s.changed && s.plan.rearm => Some(AKey { origin: s.origin, at, token: s.token }),
        _ => None,
    }
}

/// The plan once the key is armed.

pub open spec fn spec_production_plan_after(s: ASequence) -> ACommit {
    match spec_production_arms(s) {
        Some(key) => spec_production_armed(s.plan, key),
        None => s.plan,
    }
}

/// The calls a commit makes, in order, against a store that serves every
/// call: the key armed, the document written under the version loaded, the
/// key replaced removed, the key fired collected.

pub open spec fn spec_production_calls(s: ASequence, n: ANode) -> Seq<AAct> {
    let arm = match spec_production_arms(s) { Some(key) => seq![AAct::PutKey(key)], None => Seq::empty() };
    let write = if s.changed || s.fired is Some { seq![AAct::Write { cond: s.etag, idle: !s.changed }] } else { Seq::empty() };
    let disarm = match spec_production_to_disarm(spec_production_plan_after(s)) {
        Some(previous) if s.changed => seq![AAct::DeleteKey { key: previous, by: n.id }],
        _ => Seq::empty(),
    };
    let collect = match s.fired {
        Some(f) => seq![AAct::DeleteKey { key: f.key, by: f.by }],
        None => Seq::empty(),
    };
    let done = seq![AAct::Done { deleted: s.fired is Some }];
    arm + write + disarm + collect + done
}

/// The node once the commit is over: the key kept is remembered with the
/// version written, and the fired key, if it was the one remembered, forgotten.

pub open spec fn spec_production_node_after(s: ASequence, n: ANode, tag: Seq<char>) -> ANode {
    let n = if s.changed { spec_production_finish(n, spec_production_plan_after(s), tag) } else { n };
    match s.fired {
        Some(f) => spec_production_collected(n, s.origin, f.key),
        None => n,
    }
}

/// The sequence: from `Start`, against a store that serves every call, a
/// commit makes exactly `spec_production_calls`, in that order, and leaves the node as
/// `spec_production_node_after`.

/// Prepare a commit on `o`, having loaded version `etag`: the previous key
/// is the one remembered for `o` if it was armed with that very version
/// and is not the key being fired; a key is armed if the document changed,
/// owes a deadline, and the previous key is not at that instant.
pub open spec fn spec_production_prepare(n: ANode, o: Seq<char>, etag: Option<Seq<char>>, deadline: Option<nat>, changed: bool, fired: Option<AKey>) -> ACommit {
    let previous = if n.armed.contains_key(o) && Some(n.armed[o].etag) == etag && Some(n.armed[o].key) != fired { Some(n.armed[o].key) } else { None };
    let rearm = changed && match deadline {
        None => false,
        Some(d) => match previous { Some(p) => p.at != d, None => true },
    };
    ACommit { origin: o, deadline, changed, fired, previous, rearm, armed_now: None }
}

pub open spec fn spec_production_armed(t: ACommit, k: AKey) -> ACommit {
    ACommit { armed_now: Some(k), ..t }
}

/// After the write: the previous key, when it was replaced or the document
/// owes no deadline any more.
pub open spec fn spec_production_to_disarm(t: ACommit) -> Option<AKey> {
    if t.changed && (t.deadline is None || t.rearm) { t.previous } else { None }
}

/// After the write: the key the node remembers for the origin.
pub open spec fn spec_production_keep(t: ACommit) -> Option<AKey> {
    if t.deadline is None { None } else if t.rearm { t.armed_now } else { t.previous }
}

/// After the write, at version `etag`: remember the key kept with that version.
pub open spec fn spec_production_finish(n: ANode, t: ACommit, etag: Seq<char>) -> ANode {
    match spec_production_keep(t) {
        Some(k) => spec_production_set_armed(n, t.origin, Some(AArmed { key: k, etag })),
        None => spec_production_set_armed(n, t.origin, None),
    }
}

pub open spec fn production_opt_nat(o: Option<u64>) -> Option<nat> {
    match o {
        Some(x) => Some(x as nat),
        None => None,
    }
}

pub open spec fn production_opt_str(o: Option<&String>) -> Option<Seq<char>> {
    match o {
        Some(s) => Some(s@),
        None => None,
    }
}


pub uninterp spec fn production_hash(origin: Seq<char>) -> nat;

/// `production_hash(o) mod n` over the members in order.
pub open spec fn spec_production_owner(members: Seq<Seq<char>>, o: Seq<char>) -> Option<Seq<char>> {
    if members.len() == 0 { None } else { Some(members[(production_hash(o) % members.len()) as int]) }
}

pub open spec fn spec_production_fresh(n: ANode, now: nat) -> bool {
    n.read_any && n.last_read + n.ttl >= now
}

/// The node acts as owner of `o`: fresh, and the owner per its members.
pub open spec fn spec_production_acts(n: ANode, o: Seq<char>, now: nat) -> bool {
    &&& spec_production_fresh(n, now)
    &&& spec_production_owner(n.members, o) == Some(n.id)
}

/// Take on the configuration read at `now`.
pub open spec fn spec_production_read_config(n: ANode, now: nat, epoch: nat, members: Seq<Seq<char>>) -> ANode {
    ANode {
        read_any: true,
        epoch,
        members,
        last_read: now,
        ..n
    }
}

/// Remember the version of `o` read from, or written to, the bucket at `now`.
pub open spec fn spec_production_filled(n: ANode, o: Seq<char>, etag: Seq<char>, now: nat) -> ANode {
    ANode { cache: n.cache.insert(o, AEntry { etag, filled_at: now }), ..n }
}

/// Drop what is remembered of `o`.
pub open spec fn spec_production_forget(n: ANode, o: Seq<char>) -> ANode {
    ANode { cache: n.cache.remove(o), ..n }
}

/// Remember the key armed for `o` and the version written with it, or that
/// none is.
pub open spec fn spec_production_set_armed(n: ANode, o: Seq<char>, a: Option<AArmed>) -> ANode {
    match a {
        Some(a) => ANode { armed: n.armed.insert(o, a), ..n },
        None => ANode { armed: n.armed.remove(o), ..n },
    }
}

/// A fired key was collected: if it is the one remembered for `o`, forget it.
pub open spec fn spec_production_collected(n: ANode, o: Seq<char>, k: AKey) -> ANode {
    if n.armed.contains_key(o) && n.armed[o].key == k { ANode { armed: n.armed.remove(o), ..n } } else { n }
}


pub open spec fn note_effect_keys(notes: Seq<NoteV>) -> Seq<ProtocolEffectKeyV> {
    notes.map_values(
        |note: NoteV| crate::handler::protocol_effect_key(note_effect(note)),
    )
}

pub open spec fn note_effects(notes: Seq<NoteV>) -> ISet<ProtocolEffectV> {
    ISet::new(|effect: ProtocolEffectV|
        exists|i: int| 0 <= i < notes.len() && note_effect(notes[i]) == effect)
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

pub open spec fn request_document(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(origin(q.id@)),
        Request::PromiseCreate(q) => Some(origin(q.id@)),
        Request::PromiseSettle(q) => Some(origin(q.id@)),
        Request::PromiseRegisterCallback(q) => Some(origin(q.awaited@)),
        Request::PromiseRegisterListener(q) => Some(origin(q.awaited@)),
        Request::TaskGet(q) => Some(origin(q.id@)),
        Request::TaskCreate(q) => Some(origin(q.action.id@)),
        Request::TaskAcquire(q) => Some(origin(q.id@)),
        Request::TaskFulfill(q) => Some(origin(q.id@)),
        Request::TaskRelease(q) => Some(origin(q.id@)),
        Request::TaskHalt(q) => Some(origin(q.id@)),
        Request::TaskContinue(q) => Some(origin(q.id@)),
        Request::TaskFence(q) => Some(origin(q.id@)),
        Request::TaskFenceCheck(q) => Some(origin(q.id@)),
        Request::TaskSuspend(q) => Some(origin(q.id@)),
        Request::TaskHeartbeat(q) =>
            if q.tasks@.len() == 0 { None } else { Some(origin(q.tasks@[0].id@)) },
        Request::ScheduleGet(q) => Some(q.id@),
        Request::ScheduleCreate(q) => Some(q.id@),
        Request::ScheduleDelete(q) => Some(q.id@),
    }
}

pub open spec fn on_request(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
    limit: nat,
) -> StoredDocumentV {
    let (body, response, _, _) = spec_request_transition(
        spec_stored_body(document),
        request,
        now,
        retry_timeout,
        limit,
    );
    if response == spec_unavailable(request) {
        document
    } else if body == spec_stored_body(document) {
        document
    } else {
        spec_advance_stored(document, body, now)
    }
}

#[via_fn]
proof fn spec_lossy_decreases(bytes: Seq<u8>) {
    if bytes.len() > 0 {
        let width = spec_utf8_width(bytes[0]);
        if width >= 2 {
            lemma_prefix_bounds(bytes, width, 1);
        }
    }
}

#[via_fn]
proof fn spec_sorted_decreases(keys: Set<Seq<char>>) {
    if keys.finite() && keys.len() > 0 {
        lemma_min_key_present(keys);
    }
}

pub open spec fn on_event(state: Proc, now: Time, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<Proc, Pid, Message>> {
    match state {
        Proc::Node(node) => spec_node(node, now, event),
        Proc::Store(store) => spec_store(store, event),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply_change<V>(entries: Map<Seq<char>, V>, change: ChangeV<V>) -> Map<Seq<char>, V> {
    match change {
        ChangeV::Upsert { id, value } => entries.insert(id, value),
        ChangeV::Remove { id } => entries.remove(id),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply_changes<V>(entries: Map<Seq<char>, V>, changes: Seq<ChangeV<V>>) -> Map<Seq<char>, V>
    decreases changes.len(),
{
    if changes.len() == 0 {
        entries
    } else {
        spec_apply_change(spec_apply_changes(entries, changes.drop_last()), changes.last())
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply_document<V>(document: FoldedV<V>, partial: PartialV<V>) -> FoldedV<V> {
    FoldedV {
        document: document.document,
        version: partial.version,
        committed_at: partial.committed_at,
        next_wake_at: partial.next_wake_at,
        entries: spec_apply_changes(document.entries, partial.changes),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_compose<V>(first: PartialV<V>, second: PartialV<V>) -> PartialV<V> {
    PartialV {
        document: first.document,
        basever: first.basever,
        version: second.version,
        committed_at: second.committed_at,
        next_wake_at: second.next_wake_at,
        changes: first.changes + second.changes,
    }
}

pub open spec fn protocol_effect_key(effect: ProtocolEffectV) -> ProtocolEffectKeyV {
    match effect {
        ProtocolEffectV::Execute { id, .. } => ProtocolEffectKeyV::Execute { id },
        ProtocolEffectV::Unblock { promise, address, .. } =>
            ProtocolEffectKeyV::Unblock { promise, address },
    }
}

pub open spec fn promise_effect(id: Seq<char>, promise: PromV) -> PromiseEffectV {
    PromiseEffectV {
        id,
        state: promise.state,
        param: promise.param,
        value: promise.value,
        tags: promise.tags,
        timeout_at: promise.timeout_at,
        created_at: promise.created_at,
        settled_at: promise.settled_at,
    }
}

pub open spec fn offer_committed(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    committed_at: u64,
) -> bool {
    after.contains_key(id)
        && match after[id].task {
            Some(new) => {
                &&& after[id].promise.state == PromiseState::Pending
                &&& new.state == TaskState::Pending
                &&& new.retry_timeout_at is Some
                &&& new.retry_timeout_at.unwrap() > committed_at
                &&& (!before.contains_key(id) || before[id] != after[id])
                &&& if before.contains_key(id) {
                    match before[id].task {
                        Some(old) if old.state == TaskState::Pending =>
                            match old.retry_timeout_at {
                                Some(at) => at <= committed_at,
                                None => true,
                            },
                        _ => true,
                    }
                } else {
                    true
                }
            },
            None => false,
        }
}

pub open spec fn listener_committed(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    address: Seq<char>,
) -> bool {
    before.contains_key(promise)
        && before[promise].promise.listeners.contains(address)
        && after.contains_key(promise)
        && after[promise].promise.state != PromiseState::Pending
        && !after[promise].promise.listeners.contains(address)
}

pub open spec fn workflow_effects(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    committed_at: u64,
) -> ISet<ProtocolEffectV> {
    ISet::new(|effect: ProtocolEffectV| match effect {
        ProtocolEffectV::Execute { id, version } =>
            offer_committed(before, after, id, committed_at)
                && after[id].task.unwrap().version == version,
        ProtocolEffectV::Unblock { promise, address, record } =>
            listener_committed(before, after, promise, address)
                && record == promise_effect(promise, after[promise].promise),
    })
}

pub open spec fn document_effects(
    before: StoredDocumentV,
    after: StoredDocumentV,
) -> ISet<ProtocolEffectV> {
    match (before, after) {
        (StoredDocumentV::Workflow(old), StoredDocumentV::Workflow(new)) =>
            workflow_effects(old.objects, new.objects, new.committed_at),
        _ => ISet::empty(),
    }
}

pub open spec fn stored_next_wake_at(document: StoredDocumentV) -> Option<u64> {
    match document {
        StoredDocumentV::Workflow(workflow) => workflow.next_wake_at,
        StoredDocumentV::Schedule(schedule) => schedule.next_wake_at,
    }
}

pub open spec fn document_timer_effects(
    before: StoredDocumentV,
    after: StoredDocumentV,
) -> ISet<TimerEffectV> {
    let old = stored_next_wake_at(before);
    let new = stored_next_wake_at(after);
    ISet::new(|effect: TimerEffectV| match effect {
        TimerEffectV::Add { at } => new == Some(at) && new != old,
        TimerEffectV::Delete { at } => old == Some(at) && old != new,
    })
}

#[verifier::opaque]
pub open spec fn spec_string(chars: Seq<char>) -> String {
    choose|s: String| s@ == chars
}

#[verifier::opaque]
pub open spec fn spec_bytes(body: Seq<u8>) -> Vec<u8> {
    choose|v: Vec<u8>| v@ == body
}

pub open spec fn spec_one(state: Proc, send: Seq<(Pid, Message)>) -> Seq<StepResultV<Proc, Pid, Message>> {
    seq![StepResultV { state, send }]
}

pub open spec fn spec_clock(logic: LogicV, now: Time) -> LogicV {
    LogicV { clock: now as nat, ..logic }
}

// Node
pub open spec fn spec_node(node: NodeV, now: Time, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<Proc, Pid, Message>> {
    match event {
        ProcessEvent::Timeout => match node.wake {
            Some(at) if at <= now as nat && node.flight is None && node.next_op < u64::MAX => {
                let (next, send) = spec_timeout(node, now);
                spec_one(Proc::Node(NodeV {
                    logic: LogicV { clock: now as nat, last_wake: None, ..node.logic },
                    wake: spec_wake(next),
                    ..next
                }), send)
            },
            Some(at) if at <= now as nat => spec_one(Proc::Node(node), Seq::empty()),
            _ => Seq::empty(),
        },
        ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(request) } => {
            if node.flight is Some || node.next_op == u64::MAX {
                spec_one(Proc::Node(node), Seq::empty())
            } else {
                let (next, send) = spec_request(node, now, request);
                spec_one(Proc::Node(NodeV {
                    logic: spec_clock(node.logic, now),
                    next_request: (node.next_request + 1) as u64,
                    wake: spec_wake(next),
                    ..next
                }), send)
            }
        },
        ProcessEvent::Receive { sender: Pid::Store, message: Message::StoreRes { op, response } } => {
            if node.flight is None || node.next_op == u64::MAX {
                spec_one(Proc::Node(node), Seq::empty())
            } else {
                let (next, send) = spec_store_reply(node, op, response);
                spec_one(Proc::Node(NodeV {
                    logic: spec_clock(node.logic, now),
                    wake: spec_wake(next),
                    ..next
                }), send)
            }
        },
        ProcessEvent::Receive { sender: Pid::Outside, message: Message::Stop } => {
            spec_one(Proc::Node(NodeV {
                logic: LogicV { clock: now as nat, loops: false, stopping: true, ..node.logic },
                ..node
            }), Seq::empty())
        },
        _ => Seq::empty(),
    }
}

// Store
pub open spec fn spec_store(store: StoreV, event: ProcessEvent<Pid, Message>) -> Seq<StepResultV<Proc, Pid, Message>> {
    match event {
        ProcessEvent::Receive { sender, message: Message::StoreReq { op, request } } => {
            if store.seen.contains((sender, op)) {
                spec_one(Proc::Store(store), Seq::empty())
            } else {
                let (next, response) = spec_apply(store, request);
                spec_one(
                    Proc::Store(StoreV { seen: store.seen.push((sender, op)), ..next }),
                    seq![(sender, Message::StoreRes { op, response })],
                )
            }
        },
        _ => Seq::empty(),
    }
}

pub open spec fn spec_reply(client: Seq<char>, id: u64, response: Response) -> (Pid, Message) {
    (Pid::Outside, Message::Output(Output::Response { client: spec_string(client), id, response }))
}

pub open spec fn spec_get(op: u64, key: Seq<char>) -> (Pid, Message) {
    (Pid::Store, Message::StoreReq { op, request: StoreReq::Get { key: spec_string(key) } })
}

pub open spec fn spec_notify(note: NoteV) -> (Pid, Message) {
    let dispatch = match note {
        NoteV::Execute { id, version } => echod_types::Dispatch::Execute { id: spec_string(id), version },
        NoteV::Unblock { address, promise } => echod_types::Dispatch::Unblock { address: spec_string(address), promise },
    };
    (Pid::Outside, Message::Output(Output::Dispatch(dispatch)))
}

pub open spec fn spec_notes(notes: Seq<NoteV>) -> Seq<(Pid, Message)>
    decreases notes.len(),
{
    if notes.len() == 0 { Seq::empty() }
    else { seq![spec_notify(notes[0])] + spec_notes(notes.drop_first()) }
}

pub open spec fn spec_stored_body(d: StoredDocumentV) -> DocumentBodyV {
    match d {
        StoredDocumentV::Workflow(doc) => DocumentBodyV::Workflow(doc.objects),
        StoredDocumentV::Schedule(doc) => DocumentBodyV::Schedule(doc.schedule),
    }
}

pub open spec fn spec_stored_version(d: StoredDocumentV) -> u64 {
    match d {
        StoredDocumentV::Workflow(doc) => doc.version,
        StoredDocumentV::Schedule(doc) => doc.version,
    }
}

pub open spec fn spec_stored_committed_at(d: StoredDocumentV) -> u64 {
    match d {
        StoredDocumentV::Workflow(doc) => doc.committed_at,
        StoredDocumentV::Schedule(doc) => doc.committed_at,
    }
}

pub open spec fn spec_stored_next_wake_at(d: StoredDocumentV) -> Option<u64> {
    match d {
        StoredDocumentV::Workflow(doc) => doc.next_wake_at,
        StoredDocumentV::Schedule(doc) => doc.next_wake_at,
    }
}

pub open spec fn spec_stored_name(d: StoredDocumentV) -> Seq<char> {
    match d {
        StoredDocumentV::Workflow(doc) => doc.document,
        StoredDocumentV::Schedule(doc) => doc.document,
    }
}

pub open spec fn spec_empty_stored_workflow(document: Seq<char>) -> StoredDocumentV {
    StoredDocumentV::Workflow(WorkflowDocumentV {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        objects: Map::empty(),
    })
}

pub open spec fn spec_empty_stored_schedule(document: Seq<char>) -> StoredDocumentV {
    StoredDocumentV::Schedule(ScheduleDocumentV {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        schedule: None,
    })
}

pub open spec fn spec_advance_stored(
    before: StoredDocumentV,
    body: DocumentBodyV,
    committed_at: u64,
) -> StoredDocumentV {
    let version = spec_stored_version(before).saturating_add(1);
    let next_wake_at = match spec_body_deadline(body) {
        Some(at) => Some(at as u64),
        None => None,
    };
    match body {
        DocumentBodyV::Workflow(objects) => StoredDocumentV::Workflow(WorkflowDocumentV {
            document: spec_stored_name(before),
            version,
            committed_at,
            next_wake_at,
            objects,
        }),
        DocumentBodyV::Schedule(schedule) => StoredDocumentV::Schedule(ScheduleDocumentV {
            document: spec_stored_name(before),
            version,
            committed_at,
            next_wake_at,
            schedule,
        }),
    }
}

pub open spec fn spec_body_len(d: DocumentBodyV) -> nat {
    match d {
        DocumentBodyV::Workflow(m) => m.dom().len(),
        DocumentBodyV::Schedule(Some(_)) => 1,
        DocumentBodyV::Schedule(None) => 0,
    }
}

pub open spec fn nat_v(o: Option<u64>) -> Option<nat> {
    match o { Some(x) => Some(x as nat), None => None }
}

pub open spec fn spec_sent(reply: Option<(Seq<char>, u64, Response)>, notes: Seq<NoteV>) -> Seq<(Pid, Message)> {
    (match reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    }) + spec_notes(notes)
}

pub open spec fn spec_note_key(note: NoteV) -> NoteKeyV {
    match note {
        NoteV::Execute { id, .. } => NoteKeyV::Execute(id),
        NoteV::Unblock { address, promise } => NoteKeyV::Unblock(promise.id@, address),
    }
}

pub open spec fn spec_note_relevant(doc: DocumentBodyV, note: NoteV) -> bool {
    match note {
        NoteV::Execute { id, version } => {
            let objects = spec_workflow_map(doc);
            objects.contains_key(id)
                && match objects[id].task {
                    Some(task) => task.state == TaskState::Pending && task.version == version,
                    None => false,
                }
        },
        NoteV::Unblock { .. } => true,
    }
}

pub open spec fn spec_keyed_insert(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    note: NoteV,
) -> Seq<NoteV> {
    if !spec_note_relevant(doc, note) || exists|i: int| 0 <= i < notes.len()
        && spec_note_key(notes[i]) == spec_note_key(note)
    {
        notes
    } else {
        notes.push(note)
    }
}

pub open spec fn spec_keyed_notes(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        spec_keyed_insert(
            doc,
            spec_keyed_notes(doc, notes, (count - 1) as nat),
            notes[count as int - 1],
        )
    }
}

pub open spec fn spec_execute_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    committed_at: u64,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_execute_notes(before, after, committed_at, keys, (count - 1) as nat);
        let id = keys[count as int - 1];
        if crate::handler::offer_committed(before, after, id, committed_at) {
            prior.push(NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            })
        } else {
            prior
        }
    }
}

pub open spec fn spec_unblock_notes_for(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        let address = listeners[count as int - 1];
        if crate::handler::listener_committed(before, after, promise, address) {
            prior.push(NoteV::Unblock {
                address,
                promise: spec_record(spec_string(promise), after[promise].promise),
            })
        } else {
            prior
        }
    }
}

pub open spec fn spec_unblock_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_unblock_notes(before, after, keys, (count - 1) as nat);
        let promise = keys[count as int - 1];
        prior + spec_unblock_notes_for(
            before,
            after,
            promise,
            before[promise].promise.listeners,
            before[promise].promise.listeners.len(),
        )
    }
}

pub open spec fn spec_committed_notes(
    before: DocumentBodyV,
    after: DocumentBodyV,
    committed_at: u64,
) -> Seq<NoteV> {
    match (before, after) {
        (DocumentBodyV::Workflow(old), DocumentBodyV::Workflow(new)) => {
            let new_keys = spec_sorted_present(new);
            let old_keys = spec_sorted_present(old);
            spec_execute_notes(old, new, committed_at, new_keys, new_keys.len())
                + spec_unblock_notes(old, new, old_keys, old_keys.len())
        },
        _ => Seq::empty(),
    }
}

pub uninterp spec fn spec_decode_body_raw(body: Seq<u8>) -> Option<DocumentBodyV>;

pub uninterp spec fn spec_encode_body(doc: DocumentBodyV) -> Seq<u8>;

pub axiom fn axiom_decode_encode_body(doc: DocumentBodyV)
    ensures
        spec_decode_body_raw(spec_encode_body(doc)) == Some(doc),
;

pub open spec fn spec_read(key: Seq<char>, body: Seq<u8>) -> DocumentBodyV {
    match spec_decode_body_raw(body) {
        Some(doc) => doc,
        None => spec_empty_body(key),
    }
}

pub open spec fn spec_empty_value() -> Value {
    Value::spec_empty()
}

pub open spec fn spec_owns(node: NodeV, key: Seq<char>) -> bool {
    node.nodes != 0 && spec_fnv(key) % (node.nodes as u64) == (node.address as u64)
}

pub open spec fn spec_cached(node: NodeV, key: Seq<char>) -> Option<CachedV> {
    spec_cached_from(node.documents, key, 0)
}

pub open spec fn spec_cached_from(docs: Seq<CachedV>, key: Seq<char>, i: int) -> Option<CachedV>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() { None }
    else if docs[i].key == key { Some(docs[i]) }
    else { spec_cached_from(docs, key, i + 1) }
}

pub open spec fn spec_body_is_empty(doc: DocumentBodyV) -> bool {
    match doc {
        DocumentBodyV::Workflow(map) => map.dom().len() == 0,
        DocumentBodyV::Schedule(slot) => slot is None,
    }
}

pub open spec fn spec_keep(docs: Seq<CachedV>, key: Seq<char>, doc: DocumentBodyV, etag: Option<Seq<char>>) -> Seq<CachedV> {
    if spec_body_is_empty(doc) && etag is None {
        spec_forget(docs, key, 0)
    } else {
        spec_remember(docs, key, spec_encode_body(doc), etag, 0)
    }
}

pub open spec fn spec_remember(docs: Seq<CachedV>, key: Seq<char>, body: Seq<u8>, etag: Option<Seq<char>>, i: int) -> Seq<CachedV>
    decreases docs.len() - i,
{
    let entry = CachedV { key, body, etag };
    if i >= docs.len() {
        docs.push(entry)
    } else if docs[i].key == key {
        docs.update(i, entry)
    } else {
        spec_remember(docs, key, body, etag, i + 1)
    }
}

pub open spec fn spec_forget(docs: Seq<CachedV>, key: Seq<char>, i: int) -> Seq<CachedV>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() { docs }
    else if docs[i].key == key { docs.take(i) + docs.skip(i + 1) }
    else { spec_forget(docs, key, i + 1) }
}

pub open spec fn spec_request(node: NodeV, now: Time, call: Call) -> (NodeV, Seq<(Pid, Message)>) {
    match spec_key(call.request) {
        None => (node, seq![spec_reply(call.client@, call.id, spec_pure(call.request))]),
        Some(key) => {
            if !spec_owns(node, key) {
                (node, seq![spec_reply(call.client@, call.id, spec_unavailable(call.request))])
            } else {
                spec_begin(node, key, JobV::External(call.request), now, Some((call.client@, call.id)))
            }
        },
    }
}

pub open spec fn spec_timeout(node: NodeV, now: Time) -> (NodeV, Seq<(Pid, Message)>) {
    if node.flight is Some {
        (node, Seq::empty())
    } else if node.pending.len() > 0 {
        let pending = node.pending[0];
        let node = NodeV { pending: node.pending.skip(1), ..node };
        let key = spec_origin_key(origin(pending.promise));
        if !spec_owns(node, key) {
            (node, Seq::empty())
        } else {
            spec_begin(node, key, JobV::Occurrence(pending), now, None)
        }
    } else {
        match spec_earliest_key(node, now) {
            Some(key) => spec_begin(node, key, JobV::Due, now, None),
            None => (node, Seq::empty()),
        }
    }
}

pub open spec fn spec_store_reply(node: NodeV, op: u64, response: StoreRes) -> (NodeV, Seq<(Pid, Message)>) {
    match node.flight {
        None => (node, Seq::empty()),
        Some(flight) => {
            if flight.op != op {
                (node, Seq::empty())
            } else if !flight.writing {
                match response {
                    StoreRes::Get { result: Ok(got) } => {
                        let (doc, etag) = match got {
                            Some((body, tag)) => (spec_read(flight.key, body@), Some(tag.0@)),
                            None => (spec_empty_body(flight.key), None),
                        };
                        let flight = FlightV { etag, ..flight };
                        spec_decide(NodeV { flight: None, ..node }, flight, doc)
                    },
                    StoreRes::Get { result: Err(_) } => spec_fail(NodeV { flight: None, ..node }, flight),
                    _ => (node, Seq::empty()),
                }
            } else {
                match response {
                    StoreRes::PutIfMatch { result: Ok(tag) }
                    | StoreRes::PutIfNoneMatch { result: Ok(tag) } =>
                        spec_commit(node, flight, tag),
                    StoreRes::PutIfMatch { result: Err(_) }
                    | StoreRes::PutIfNoneMatch { result: Err(_) } =>
                        spec_fail(NodeV { flight: None, ..node }, flight),
                    _ => (node, Seq::empty()),
                }
            }
        },
    }
}

pub open spec fn spec_flight(op: u64, key: Seq<char>, etag: Option<Seq<char>>, now: Time, caller: Option<(Seq<char>, u64)>, job: JobV) -> FlightV {
    FlightV {
        op,
        key,
        writing: false,
        etag,
        now,
        caller,
        job,
        born: Seq::empty(),
        reply: None,
        notify: Seq::empty(),
        decided: None,
    }
}

pub open spec fn spec_begin(node: NodeV, key: Seq<char>, job: JobV, now: Time, caller: Option<(Seq<char>, u64)>) -> (NodeV, Seq<(Pid, Message)>) {
    match spec_cached(node, key) {
        Some(cached) => spec_decide(node, spec_flight(0, key, cached.etag, now, caller, job), spec_read(key, cached.body)),
        None => {
            let op = node.next_op;
            let flight = spec_flight(op, key, None, now, caller, job);
            (NodeV { flight: Some(flight), next_op: (op + 1) as u64, ..node }, seq![spec_get(op, key)])
        },
    }
}

pub open spec fn spec_decide(node: NodeV, flight: FlightV, doc: DocumentBodyV) -> (NodeV, Seq<(Pid, Message)>) {
    let (next, reply, born, notify) = match flight.job {
        JobV::External(request) => {
            let (next, response) = spec_handle(doc, request, flight.now);
            (next, Some(response), Seq::empty(), Seq::empty())
        },
        JobV::Due => spec_run_due(doc, flight.now, node.retry_timeout),
        JobV::Occurrence(pending) => (spec_occurrence(doc, pending, flight.now), None, Seq::empty(), Seq::empty()),
    };
    let reply = match (flight.caller, reply) {
        (Some((client, id)), Some(response)) => Some((client, id, response)),
        _ => None,
    };
    let previous = match spec_cached(node, flight.key) {
        Some(cached) => spec_read(flight.key, cached.body),
        None => spec_empty_body(flight.key),
    };
    if next == previous && born.len() == 0 {
        let node = NodeV {
            flight: None,
            documents: spec_keep(node.documents, flight.key, next, flight.etag),
            ..node
        };
        let send = match reply {
            Some((client, id, response)) => seq![spec_reply(client, id, response)],
            None => Seq::empty(),
        };
        (node, send + spec_notes(notify))
    } else {
        let op = node.next_op;
        let body = spec_encode_body(next);
        let request = match flight.etag {
            Some(chars) => StoreReq::PutIfMatch {
                key: spec_string(flight.key),
                body: spec_bytes(body),
                etag: Etag(spec_string(chars)),
            },
            None => StoreReq::PutIfNoneMatch { key: spec_string(flight.key), body: spec_bytes(body) },
        };
        let flight = FlightV {
            op,
            writing: true,
            born,
            reply,
            notify,
            decided: Some(body),
            ..flight
        };
        (NodeV { flight: Some(flight), next_op: (op + 1) as u64, ..node }, seq![(Pid::Store, Message::StoreReq { op, request })])
    }
}

pub open spec fn spec_commit(node: NodeV, flight: FlightV, tag: Etag) -> (NodeV, Seq<(Pid, Message)>) {
    let documents = match flight.decided {
        Some(body) => spec_remember(node.documents, flight.key, body, Some(tag.0@), 0),
        None => node.documents,
    };
    let node = NodeV {
        flight: None,
        documents,
        pending: node.pending + flight.born,
        ..node
    };
    let send = match flight.reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    };
    (node, send + spec_notes(flight.notify))
}

pub open spec fn spec_fail(node: NodeV, flight: FlightV) -> (NodeV, Seq<(Pid, Message)>) {
    match (flight.job, flight.caller) {
        (JobV::External(request), Some((client, id))) => {
            (node, seq![spec_reply(client, id, spec_unavailable(request))])
        },
        _ => (node, Seq::empty()),
    }
}

pub open spec fn spec_origin_key(origin_chars: Seq<char>) -> Seq<char> {
    seq!['o', '/'] + origin_chars
}

pub open spec fn spec_schedule_key(id: Seq<char>) -> Seq<char> {
    seq!['s', '/'] + id
}

pub open spec fn spec_empty_body(key: Seq<char>) -> DocumentBodyV {
    if spec_starts(key, seq!['s', '/']) { DocumentBodyV::Schedule(None) } else { DocumentBodyV::Workflow(Map::empty()) }
}

pub open spec fn spec_key(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseCreate(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseSettle(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseRegisterCallback(q) => Some(spec_origin_key(origin(q.awaited@))),
        Request::PromiseRegisterListener(q) => Some(spec_origin_key(origin(q.awaited@))),
        Request::TaskGet(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskCreate(q) => Some(spec_origin_key(origin(q.action.id@))),
        Request::TaskAcquire(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFulfill(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskRelease(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskHalt(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskContinue(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFence(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFenceCheck(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskSuspend(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskHeartbeat(q) => {
            if q.tasks@.len() == 0 { None } else { Some(spec_origin_key(origin(q.tasks@[0].id@))) }
        },
        Request::ScheduleGet(q) => Some(spec_schedule_key(q.id@)),
        Request::ScheduleDelete(q) => Some(spec_schedule_key(q.id@)),
        Request::ScheduleCreate(q) => Some(spec_schedule_key(q.id@)),
    }
}

pub open spec fn spec_request_document(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(origin(q.id@)),
        Request::PromiseCreate(q) => Some(origin(q.id@)),
        Request::PromiseSettle(q) => Some(origin(q.id@)),
        Request::PromiseRegisterCallback(q) => Some(origin(q.awaited@)),
        Request::PromiseRegisterListener(q) => Some(origin(q.awaited@)),
        Request::TaskGet(q) => Some(origin(q.id@)),
        Request::TaskCreate(q) => Some(origin(q.action.id@)),
        Request::TaskAcquire(q) => Some(origin(q.id@)),
        Request::TaskFulfill(q) => Some(origin(q.id@)),
        Request::TaskRelease(q) => Some(origin(q.id@)),
        Request::TaskHalt(q) => Some(origin(q.id@)),
        Request::TaskContinue(q) => Some(origin(q.id@)),
        Request::TaskFence(q) => Some(origin(q.id@)),
        Request::TaskFenceCheck(q) => Some(origin(q.id@)),
        Request::TaskSuspend(q) => Some(origin(q.id@)),
        Request::TaskHeartbeat(q) =>
            if q.tasks@.len() == 0 { None } else { Some(origin(q.tasks@[0].id@)) },
        Request::ScheduleGet(q) => Some(q.id@),
        Request::ScheduleCreate(q) => Some(q.id@),
        Request::ScheduleDelete(q) => Some(q.id@),
    }
}

pub open spec fn spec_promise_res(status: u16, promise: Option<PromiseRecord>) -> Response {
    Response::Promise(PromiseRes { status, promise })
}

pub open spec fn spec_pure(request: Request) -> Response {
    match request {
        Request::TaskHeartbeat(q) if q.tasks@.len() == 0 => Response::Status(StatusRes { status: 200 }),
        other => spec_unavailable(other),
    }
}

pub open spec fn spec_unavailable(request: Request) -> Response {
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => spec_promise_res(503, None),
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => Response::Schedule(ScheduleRes { status: 503, schedule: None }),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => Response::Status(StatusRes { status: 503 }),
        Request::TaskGet(_) => Response::TaskGet(TaskGetRes { status: 503, task: None }),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => Response::TaskClaim(TaskClaimRes { status: 503, task: None, promise: None }),
        Request::TaskFulfill(_) => spec_promise_res(503, None),
        Request::TaskFence(_) => Response::TaskFence(TaskFenceRes { status: 503, action: None }),
    }
}

pub open spec fn spec_handle(doc: DocumentBodyV, request: Request, now: Time) -> (DocumentBodyV, Response) {
    match request {
        Request::PromiseGet(q) => spec_promise_get(doc, q.id, now),
        Request::PromiseCreate(q) => spec_promise_create(doc, q, now),
        Request::PromiseSettle(q) => spec_promise_settle(doc, q, now),
        Request::PromiseRegisterCallback(q) => spec_register_callback(doc, q.awaited, q.awaiter, now),
        Request::PromiseRegisterListener(q) => spec_register_listener(doc, q.awaited, q.address, now),
        Request::TaskGet(q) => spec_task_get(doc, q.id, now),
        Request::TaskCreate(q) => spec_task_create(doc, q.pid, q.ttl, q.action, now),
        Request::TaskAcquire(q) => spec_task_acquire(doc, q.id, q.version, q.pid, q.ttl, now),
        Request::TaskFulfill(q) => spec_task_fulfill(doc, q.id, q.version, q.action, now),
        Request::TaskRelease(q) => spec_task_release(doc, q.id, q.version, now),
        Request::TaskHalt(q) => spec_task_halt(doc, q.id, now),
        Request::TaskContinue(q) => spec_task_continue(doc, q.id, now),
        Request::TaskHeartbeat(q) => spec_heartbeat(doc, q.pid, q.tasks@, now),
        Request::TaskSuspend(q) => spec_suspend(doc, q.id, q.version, q.actions@, now),
        Request::TaskFence(q) => spec_fence(doc, q.id, q.version, q.action, now),
        Request::TaskFenceCheck(q) => spec_fence_check(doc, q.id, q.version, now),
        Request::ScheduleGet(q) => spec_schedule_get(doc, q.id),
        Request::ScheduleCreate(q) => spec_schedule_create(doc, q, now),
        Request::ScheduleDelete(q) => spec_schedule_delete(doc, q.id),
    }
}

pub open spec fn spec_workflow_map(doc: DocumentBodyV) -> Map<Seq<char>, ObjV> {
    match doc {
        DocumentBodyV::Workflow(map) => map,
        DocumentBodyV::Schedule(_) => Map::empty(),
    }
}

pub open spec fn spec_opened(doc: DocumentBodyV) -> DocumentBodyV {
    DocumentBodyV::Workflow(spec_workflow_map(doc))
}

pub open spec fn spec_with_workflow(doc: DocumentBodyV, map: Map<Seq<char>, ObjV>) -> DocumentBodyV {
    match doc {
        DocumentBodyV::Schedule(_) => DocumentBodyV::Workflow(map),
        DocumentBodyV::Workflow(_) => DocumentBodyV::Workflow(map),
    }
}

pub open spec fn spec_project_prom(p: PromV, now: Time) -> PromV {
    if p.state == PromiseState::Pending && now >= p.timeout_at {
        PromV {
            state: if spec_timer(p.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
            settled_at: Some(p.timeout_at),
            ..p
        }
    } else {
        p
    }
}

pub open spec fn spec_fulfill_task(t: TkV) -> TkV {
    TkV {
        state: TaskState::Fulfilled,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_project_obj(obj: ObjV, now: Time) -> ObjV {
    let promise = spec_project_prom(obj.promise, now);
    let task = match obj.task {
        Some(t) if promise.state != PromiseState::Pending && t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
        other => other,
    };
    ObjV { promise, task }
}

pub open spec fn spec_record(id: String, p: PromV) -> PromiseRecord {
    PromiseRecord {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        tags: p.tags,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

pub open spec fn spec_task_record(id: String, t: TkV) -> TaskRecord {
    TaskRecord {
        id,
        state: t.state,
        version: t.version,
        resumes: if t.resumes.len() > u64::MAX as nat { u64::MAX } else { t.resumes.len() as u64 },
        ttl: t.ttl,
        pid: match t.pid { Some(s) => Some(spec_string(s)), None => None },
    }
}

pub open spec fn spec_timer(tags: Tags) -> bool {
    spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r'], seq!['t','r','u','e'], 0)
}

pub open spec fn spec_targeted(tags: Tags) -> bool {
    spec_tag_key(tags, seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t'], 0)
}

pub open spec fn spec_awaitable(tags: Tags) -> bool {
    spec_targeted(tags)
        || spec_timer(tags)
        || spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'], seq!['t','r','u','e'], 0)
        || spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'], seq!['g','l','o','b','a','l'], 0)
}

pub open spec fn spec_tag_is(tags: Tags, key: Seq<char>, value: Seq<char>, i: int) -> bool
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { false }
    else if tags@[i].0@ == key { tags@[i].1@ == value }
    else { spec_tag_is(tags, key, value, i + 1) }
}

pub open spec fn spec_tag_key(tags: Tags, key: Seq<char>, i: int) -> bool
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { false }
    else if tags@[i].0@ == key { true }
    else { spec_tag_key(tags, key, i + 1) }
}

pub open spec fn spec_offer_at(tags: Tags, now: Time) -> u64 {
    match spec_delay(tags, 0) {
        Some(delay) => if delay > now { delay } else { now },
        None => now,
    }
}

pub open spec fn spec_delay(tags: Tags, i: int) -> Option<u64>
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { None }
    else if tags@[i].0@ == seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'd', 'e', 'l', 'a', 'y'] {
        spec_parse_u64(tags@[i].1@)
    } else {
        spec_delay(tags, i + 1)
    }
}

pub open spec fn spec_parse_u64(s: Seq<char>) -> Option<u64> {
    if s.len() == 0 { None } else { spec_parse_acc(s, 0, 0) }
}

pub open spec fn spec_parse_acc(s: Seq<char>, i: int, acc: nat) -> Option<u64>
    decreases s.len() - i,
{
    if i >= s.len() {
        Some(acc as u64)
    } else if s[i] < '0' || s[i] > '9' {
        None
    } else {
        let n = acc * 10 + ((s[i] as u64) - ('0' as u64)) as nat;
        if n > (u64::MAX as nat) { None } else { spec_parse_acc(s, i + 1, n) }
    }
}

pub open spec fn spec_promise_get(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, spec_promise_res(404, None))
    } else {
        let obj = spec_project_obj(map[id@], now);
        (doc, spec_promise_res(200, Some(spec_record(id, obj.promise))))
    }
}

pub open spec fn spec_new_obj(timeout_at: u64, now: Time, param: Value, tags: Tags, runnable: bool) -> ObjV {
    let live = timeout_at > now;
    let promise = PromV {
        state: if live { PromiseState::Pending } else if spec_timer(tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
        param,
        value: spec_empty_value(),
        tags,
        timeout_at,
        created_at: if live { now } else { timeout_at },
        settled_at: if live { None } else { Some(timeout_at) },
        callbacks: Seq::empty(),
        listeners: Seq::empty(),
    };
    let task = if runnable {
        Some(TkV {
            state: if live { TaskState::Pending } else { TaskState::Fulfilled },
            version: 0,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: if live { Some(now) } else { None },
            resumes: Seq::empty(),
        })
    } else {
        None
    };
    ObjV { promise, task }
}

pub open spec fn spec_promise_create(doc: DocumentBodyV, req: PromiseCreateReq, now: Time) -> (DocumentBodyV, Response) {
    if req.timeout_at > MAX_TIME || (spec_timer(req.tags) && spec_targeted(req.tags)) {
        (doc, spec_promise_res(400, None))
    } else {
        let map = spec_workflow_map(doc);
        if map.contains_key(req.id@) {
            let obj = spec_project_obj(map[req.id@], now);
            (doc, spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        } else {
            let obj = spec_new_obj(req.timeout_at, now, req.param, req.tags, spec_targeted(req.tags));
            (spec_with_workflow(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        }
    }
}

pub open spec fn spec_promise_settle(doc: DocumentBodyV, req: PromiseSettleReq, now: Time) -> (DocumentBodyV, Response) {
    if !req.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
        if !map.contains_key(req.id@) {
            (doc, spec_promise_res(404, None))
        } else {
            let seen = spec_project_obj(map[req.id@], now);
            if seen.promise.state != PromiseState::Pending {
                (doc, spec_promise_res(200, Some(spec_record(req.id, seen.promise))))
            } else {
                let promise = PromV { state: req.state, value: req.value, settled_at: Some(now), ..seen.promise };
                let task = match seen.task {
                    Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
                    other => other,
                };
                let obj = ObjV { promise, task };
                (spec_with_workflow(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
            }
        }
    }
}

pub open spec fn spec_register_callback(doc: DocumentBodyV, awaited: String, awaiter: String, now: Time) -> (DocumentBodyV, Response) {
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
        if !map.contains_key(awaited@) {
            (doc, spec_promise_res(404, None))
        } else if !map.contains_key(awaiter@) {
            (doc, spec_promise_res(422, None))
        } else {
            let awaited_obj = spec_project_obj(map[awaited@], now);
            let awaiter_obj = spec_project_obj(map[awaiter@], now);
            if !spec_targeted(awaiter_obj.promise.tags) || !spec_awaitable(awaited_obj.promise.tags) {
                (doc, spec_promise_res(422, None))
            } else {
                let res = spec_promise_res(200, Some(spec_record(awaited, awaited_obj.promise)));
                if awaited_obj.promise.state == PromiseState::Pending && awaiter_obj.promise.state == PromiseState::Pending {
                    let callbacks = if awaited_obj.promise.callbacks.contains(awaiter@) {
                        awaited_obj.promise.callbacks
                    } else {
                        awaited_obj.promise.callbacks.push(awaiter@)
                    };
                    let awaited_obj = ObjV { promise: PromV { callbacks, ..awaited_obj.promise }, ..awaited_obj };
                    (spec_with_workflow(doc, map.insert(awaited@, awaited_obj)), res)
                } else {
                    (doc, res)
                }
            }
        }
    }
}

pub open spec fn spec_register_listener(doc: DocumentBodyV, awaited: String, address: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(awaited@) {
        (doc, spec_promise_res(404, None))
    } else {
        let obj = spec_project_obj(map[awaited@], now);
        if !spec_awaitable(obj.promise.tags) {
            (doc, spec_promise_res(422, None))
        } else {
            let res = spec_promise_res(200, Some(spec_record(awaited, obj.promise)));
            if obj.promise.state == PromiseState::Pending {
                let listeners = if obj.promise.listeners.contains(address@) {
                    obj.promise.listeners
                } else {
                    obj.promise.listeners.push(address@)
                };
                let obj = ObjV { promise: PromV { listeners, ..obj.promise }, ..obj };
                (spec_with_workflow(doc, map.insert(awaited@, obj)), res)
            } else {
                (doc, res)
            }
        }
    }
}

pub open spec fn spec_task_get(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::TaskGet(TaskGetRes { status: 404, task: None }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::TaskGet(TaskGetRes { status: 404, task: None })),
            Some(t) => (doc, Response::TaskGet(TaskGetRes { status: 200, task: Some(spec_task_record(id, t)) })),
        }
    }
}

pub open spec fn spec_acquire(t: TkV, pid: Seq<char>, ttl: u64, now: Time) -> TkV {
    TkV {
        state: TaskState::Acquired,
        version: spec_sat_add(t.version, 1),
        pid: Some(pid),
        ttl: Some(ttl),
        lease_timeout_at: Some(spec_sat_add(now, ttl)),
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_task_create(doc: DocumentBodyV, pid: String, ttl: u64, action: PromiseCreateReq, now: Time) -> (DocumentBodyV, Response) {
    if ttl == 0 || ttl > MAX_TIME || action.timeout_at > MAX_TIME
        || !spec_targeted(action.tags) || spec_timer(action.tags) {
        (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
    } else {
        let (doc, created) = spec_promise_create(doc, action, now);
        match created {
            Response::Promise(inner) if inner.status == 400 => {
                (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
            },
            _ => {
                let map = spec_workflow_map(doc);
                if !map.contains_key(action.id@) {
                    (doc, Response::TaskClaim(TaskClaimRes { status: 422, task: None, promise: None }))
                } else {
                    let seen = spec_project_obj(map[action.id@], now);
                    if !spec_targeted(seen.promise.tags) {
                        (doc, Response::TaskClaim(TaskClaimRes { status: 422, task: None, promise: None }))
                    } else {
                        match seen.task {
                            None => (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None })),
                            Some(t) if t.state == TaskState::Fulfilled => (
                                doc,
                                Response::TaskClaim(TaskClaimRes {
                                    status: 200,
                                    task: Some(spec_task_record(action.id, t)),
                                    promise: Some(spec_record(action.id, seen.promise)),
                                }),
                            ),
                            Some(t) if t.state == TaskState::Pending && t.version >= MAX_VERSION => {
                                (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None }))
                            },
                            Some(t) if t.state == TaskState::Pending => {
                                let u = spec_acquire(t, pid@, ttl, now);
                                let obj = ObjV { task: Some(u), ..seen };
                                (
                                    spec_with_workflow(doc, map.insert(action.id@, obj)),
                                    Response::TaskClaim(TaskClaimRes {
                                        status: 200,
                                        task: Some(spec_task_record(action.id, u)),
                                        promise: Some(spec_record(action.id, obj.promise)),
                                    }),
                                )
                            },
                            _ => (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None })),
                        }
                    }
                }
            },
        }
    }
}

pub open spec fn spec_held(map: Map<Seq<char>, ObjV>, id: Seq<char>, version: u64, now: Time) -> (Map<Seq<char>, ObjV>, Held) {
    if !map.contains_key(id) {
        (map, Held::Missing)
    } else {
        let obj = spec_project_obj(map[id], now);
        match obj.task {
            None => (map, Held::Missing),
            Some(t) if t.state == TaskState::Acquired && t.version == version && obj.promise.state == PromiseState::Pending => (map, Held::Ok(obj)),
            _ => (map, Held::Stale),
        }
    }
}

pub open spec fn spec_task_acquire(doc: DocumentBodyV, id: String, version: u64, pid: String, ttl: u64, now: Time) -> (DocumentBodyV, Response) {
    if ttl == 0 || ttl > MAX_TIME {
        (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
        if !map.contains_key(id@) {
            (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None }))
        } else {
            let obj = spec_project_obj(map[id@], now);
            match obj.task {
                None => (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None })),
                Some(t) if t.state != TaskState::Pending || t.version != version
                    || obj.promise.state != PromiseState::Pending || t.version >= MAX_VERSION => {
                    (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None }))
                },
                Some(t) => {
                    let u = spec_acquire(t, pid@, ttl, now);
                    let obj = ObjV { task: Some(u), ..obj };
                    (
                        spec_with_workflow(doc, map.insert(id@, obj)),
                        Response::TaskClaim(TaskClaimRes {
                            status: 200,
                            task: Some(spec_task_record(id, u)),
                            promise: Some(spec_record(id, obj.promise)),
                        }),
                    )
                },
            }
        }
    }
}

pub open spec fn spec_unlease(t: TkV, state: TaskState, retry: Option<u64>) -> TkV {
    TkV { state, pid: None, ttl: None, lease_timeout_at: None, retry_timeout_at: retry, ..t }
}

pub open spec fn spec_task_release(doc: DocumentBodyV, id: String, version: u64, now: Time) -> (DocumentBodyV, Response) {
    let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(obj) => {
            let task = match obj.task { Some(t) => Some(spec_unlease(t, TaskState::Pending, Some(now))), None => None };
            (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
        },
    }
}

pub open spec fn spec_task_fulfill(doc: DocumentBodyV, id: String, version: u64, action: PromiseSettleReq, now: Time) -> (DocumentBodyV, Response) {
    if !action.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), spec_promise_res(404, None)),
            Held::Stale => (spec_with_workflow(doc, map), spec_promise_res(409, None)),
            Held::Ok(obj) => {
                let promise = PromV { state: action.state, value: action.value, settled_at: Some(now), ..obj.promise };
                let task = match obj.task { Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)), other => other };
                let obj = ObjV { promise, task };
                (spec_with_workflow(doc, map.insert(id@, obj)), spec_promise_res(200, Some(spec_record(id, obj.promise))))
            },
        }
    }
}

pub open spec fn spec_task_halt(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::Status(StatusRes { status: 404 }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::Status(StatusRes { status: 404 })),
            Some(t) if t.state == TaskState::Fulfilled => (doc, Response::Status(StatusRes { status: 409 })),
            Some(t) if t.state == TaskState::Halted => (doc, Response::Status(StatusRes { status: 200 })),
            Some(t) => {
                let obj = ObjV { task: Some(spec_unlease(t, TaskState::Halted, None)), ..obj };
                (spec_with_workflow(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_task_continue(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::Status(StatusRes { status: 404 }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::Status(StatusRes { status: 404 })),
            Some(t) if t.state != TaskState::Halted || obj.promise.state != PromiseState::Pending => {
                (doc, Response::Status(StatusRes { status: 409 }))
            },
            Some(t) => {
                let obj = ObjV { task: Some(TkV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t }), ..obj };
                (spec_with_workflow(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_heartbeat(doc: DocumentBodyV, pid: String, tasks: Seq<TaskRef>, now: Time) -> (DocumentBodyV, Response) {
    if tasks.len() == 0 {
        (doc, Response::Status(StatusRes { status: 200 }))
    } else if !spec_one_origin(tasks, origin(tasks[0].id@), 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        (spec_with_workflow(doc, spec_extend(spec_workflow_map(doc), pid@, tasks, now, 0)), Response::Status(StatusRes { status: 200 }))
    }
}

pub open spec fn spec_one_origin(tasks: Seq<TaskRef>, origin_chars: Seq<char>, i: int) -> bool
    decreases tasks.len() - i,
{
    if i < 0 || i >= tasks.len() { true }
    else { origin(tasks[i].id@) == origin_chars && spec_one_origin(tasks, origin_chars, i + 1) }
}

pub open spec fn spec_extend(map: Map<Seq<char>, ObjV>, pid: Seq<char>, tasks: Seq<TaskRef>, now: Time, i: int) -> Map<Seq<char>, ObjV>
    decreases tasks.len() - i,
{
    if i < 0 || i >= tasks.len() {
        map
    } else if !map.contains_key(tasks[i].id@) {
        spec_extend(map, pid, tasks, now, i + 1)
    } else {
        let obj = spec_project_obj(map[tasks[i].id@], now);
        match obj.task {
            Some(t) if t.state == TaskState::Acquired && t.version == tasks[i].version && t.pid == Some(pid) => {
                let ttl = match t.ttl { Some(n) => n, None => 0 };
                let at = spec_sat_add(now, ttl);
                let obj = ObjV { task: Some(TkV { lease_timeout_at: Some(at), ..t }), ..obj };
                spec_extend(map.insert(tasks[i].id@, obj), pid, tasks, now, i + 1)
            },
            _ => spec_extend(map, pid, tasks, now, i + 1),
        }
    }
}

pub open spec fn spec_suspend(doc: DocumentBodyV, id: String, version: u64, actions: Seq<PromiseRegisterCallbackReq>, now: Time) -> (DocumentBodyV, Response) {
    if actions.len() == 0 || spec_bad_suspend(actions, id@, 0) || !spec_distinct_awaited(actions, 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
            Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
            Held::Ok(obj) => {
                if spec_missing_awaited(map, actions, 0) || spec_unawaitable(map, actions, 0) {
                    (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 422 }))
                } else if spec_any_settled(map, actions, now, 0) {
                    let task = match obj.task { Some(t) => Some(TkV { resumes: Seq::empty(), ..t }), None => None };
                    (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 300 }))
                } else {
                    let map = spec_add_callbacks(map, id@, actions, 0);
                    let obj = map[id@];
                    let task = match obj.task {
                        Some(t) => Some(TkV { resumes: Seq::empty(), ..spec_unlease(t, TaskState::Suspended, None) }),
                        None => None,
                    };
                    (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
                }
            },
        }
    }
}

pub open spec fn spec_bad_suspend(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else { actions[i].awaited@ == id || !same_origin_spec(actions[i].awaited@, id) || spec_bad_suspend(actions, id, i + 1) }
}

pub open spec fn spec_distinct_awaited(actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { true }
    else { !spec_seen(actions, actions[i].awaited@, 0, i) && spec_distinct_awaited(actions, i + 1) }
}

pub open spec fn spec_seen(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, j: int, stop: int) -> bool
    decreases stop - j,
{
    if j < 0 || j >= stop || j >= actions.len() { false }
    else { actions[j].awaited@ == id || spec_seen(actions, id, j + 1, stop) }
}

pub open spec fn spec_missing_awaited(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else { !map.contains_key(actions[i].awaited@) || spec_missing_awaited(map, actions, i + 1) }
}

pub open spec fn spec_unawaitable(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else {
        (map.contains_key(actions[i].awaited@) && !spec_awaitable(map[actions[i].awaited@].promise.tags))
            || spec_unawaitable(map, actions, i + 1)
    }
}

pub open spec fn spec_any_settled(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, now: Time, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else {
        (map.contains_key(actions[i].awaited@) && spec_project_obj(map[actions[i].awaited@], now).promise.state != PromiseState::Pending)
            || spec_any_settled(map, actions, now, i + 1)
    }
}

pub open spec fn spec_add_callbacks(map: Map<Seq<char>, ObjV>, id: Seq<char>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> Map<Seq<char>, ObjV>
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { map }
    else if !map.contains_key(actions[i].awaited@) {
        spec_add_callbacks(map, id, actions, i + 1)
    } else {
        let obj = map[actions[i].awaited@];
        let callbacks = if obj.promise.callbacks.contains(id) { obj.promise.callbacks } else { obj.promise.callbacks.push(id) };
        let obj = ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj };
        spec_add_callbacks(map.insert(actions[i].awaited@, obj), id, actions, i + 1)
    }
}

pub open spec fn spec_fence(doc: DocumentBodyV, id: String, version: u64, action: TaskFenceAction, now: Time) -> (DocumentBodyV, Response) {
    let target = match action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    if target@ == id@ || !same_origin_spec(target@, id@) {
        (doc, Response::TaskFence(TaskFenceRes { status: 400, action: None }))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), Response::TaskFence(TaskFenceRes { status: 404, action: None })),
            Held::Stale => (spec_with_workflow(doc, map), Response::TaskFence(TaskFenceRes { status: 409, action: None })),
            Held::Ok(_) => {
                let doc = spec_with_workflow(doc, map);
                match action {
                    TaskFenceAction::Create(req) => {
                        let (doc, response) = spec_promise_create(doc, req, now);
                        let inner = match response { Response::Promise(p) => p, _ => PromiseRes { status: 500, promise: None } };
                        (doc, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Create(inner)) }))
                    },
                    TaskFenceAction::Settle(req) => {
                        let (doc, response) = spec_promise_settle(doc, req, now);
                        let inner = match response { Response::Promise(p) => p, _ => PromiseRes { status: 500, promise: None } };
                        (doc, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Settle(inner)) }))
                    },
                }
            },
        }
    }
}

pub open spec fn spec_fence_check(doc: DocumentBodyV, id: String, version: u64, now: Time) -> (DocumentBodyV, Response) {
    let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(_) => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 200 })),
    }
}

pub open spec fn spec_schedule_get(doc: DocumentBodyV, id: String) -> (DocumentBodyV, Response) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.id == id => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
        _ => (doc, Response::Schedule(ScheduleRes { status: 404, schedule: None })),
    }
}

pub open spec fn spec_schedule_create(doc: DocumentBodyV, req: ScheduleCreateReq, now: Time) -> (DocumentBodyV, Response) {
    let next_run_at = echod_types::common::spec_next_cron(req.cron@, now);
    if next_run_at.is_none() || !spec_deadline_bounded(next_run_at.unwrap(), req.promise_timeout)
        || (spec_targeted(req.promise_tags) && spec_timer(req.promise_tags))
    {
        (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }))
    } else {
        match doc {
            DocumentBodyV::Schedule(Some(schedule)) => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
            _ => {
                let schedule = Schedule {
                    id: req.id,
                    cron: req.cron,
                    promise_id: req.promise_id,
                    promise_timeout: req.promise_timeout,
                    promise_param: req.promise_param,
                    promise_tags: req.promise_tags,
                next_run_at,
                    last_run_at: None,
                    created_at: now,
                };
                (DocumentBodyV::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) }))
            },
        }
    }
}

pub open spec fn spec_schedule_delete(doc: DocumentBodyV, id: String) -> (DocumentBodyV, Response) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.id == id => (DocumentBodyV::Schedule(None), Response::Status(StatusRes { status: 200 })),
        _ => (doc, Response::Status(StatusRes { status: 404 })),
    }
}

pub open spec fn spec_run_due(doc: DocumentBodyV, now: Time, retry_timeout: u64) -> (DocumentBodyV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.next_run_at.is_some() && schedule.next_run_at.unwrap() <= now => {
            let at = schedule.next_run_at.unwrap();
            let pending = PendingV {
                promise: echod_types::common::spec_expand(schedule.promise_id@, schedule.id@, at),
                at,
                timeout: schedule.promise_timeout,
                param: schedule.promise_param,
                tags: schedule.promise_tags,
            };
            let schedule = Schedule {
                last_run_at: Some(at),
                next_run_at: echod_types::common::spec_next_cron(schedule.cron@, at),
                ..schedule
            };
            (DocumentBodyV::Schedule(Some(schedule)), None, seq![pending], Seq::empty())
        },
        DocumentBodyV::Workflow(map) => {
            match spec_due_id(map, spec_sorted_present(map), now) {
                Some(id) => {
                    let (map, notes) = spec_step_object(map, id, now, retry_timeout);
                    (DocumentBodyV::Workflow(map), None, Seq::empty(), notes)
                },
                None => (doc, None, Seq::empty(), Seq::empty()),
            }
        },
        other => (other, None, Seq::empty(), Seq::empty()),
    }
}

pub open spec fn spec_due_offer(obj: ObjV, now: Time) -> bool {
    obj.promise.state == PromiseState::Pending && obj.promise.timeout_at > now &&
        match obj.task {
            Some(t) =>
                (t.state == TaskState::Acquired && match t.lease_timeout_at { Some(at) => at <= now, None => false })
                || (t.state == TaskState::Pending && match t.retry_timeout_at { Some(at) => at <= now, None => false }),
            None => false,
        }
}

pub open spec fn spec_project_offers(
    map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, count: nat, now: Time,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let notes = spec_project_offers(map, keys, (count - 1) as nat, now);
        let id = keys[count as int - 1];
        if spec_due_offer(map[id], now) {
            notes.push(NoteV::Execute { id, version: map[id].task.unwrap().version })
        } else { notes }
    }
}

pub open spec fn spec_bulk_workflow(
    map: Map<Seq<char>, ObjV>, now: Time, retry_timeout: u64,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
    let keys = spec_sorted_present(map);
    let offers = spec_project_offers(map, keys, keys.len(), now);
    let projected = spec_project_workflow(map, now, retry_timeout);
    let (next, notifications) = spec_drain_workflow(projected, now, retry_timeout);
    (next, offers + notifications)
}

pub open spec fn spec_drain_listeners(
    map: Map<Seq<char>, ObjV>, id: Seq<char>,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
    if !map.contains_key(id) || map[id].promise.state == PromiseState::Pending {
        (map, Seq::empty())
    } else {
        let obj = map[id];
        (
            map.insert(id, ObjV {
                promise: PromV { listeners: Seq::empty(), ..obj.promise }, ..obj
            }),
            obj.promise.listeners.map_values(|address: Seq<char>| NoteV::Unblock {
                address, promise: spec_record(spec_string(id), obj.promise),
            }),
        )
    }
}

pub open spec fn spec_drain_callback_keys(
    map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, count: nat, now: Time, retry_timeout: u64,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>)
    decreases count,
{
    if count == 0 { (map, Seq::empty()) } else {
        let (prior, notes) = spec_drain_callback_keys(map, keys, (count - 1) as nat, now, retry_timeout);
        let (next, more) = spec_drain_settled_callbacks(prior, keys[count as int - 1], now, retry_timeout);
        (next, notes + more)
    }
}

pub open spec fn spec_drain_listener_keys(
    map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, count: nat,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>)
    decreases count,
{
    if count == 0 { (map, Seq::empty()) } else {
        let (prior, notes) = spec_drain_listener_keys(map, keys, (count - 1) as nat);
        let (next, more) = spec_drain_listeners(prior, keys[count as int - 1]);
        (next, notes + more)
    }
}

pub open spec fn spec_drain_workflow(
    map: Map<Seq<char>, ObjV>, now: Time, retry_timeout: u64,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
    let keys = spec_sorted_present(map);
    let (resumed, callbacks) = spec_drain_callback_keys(map, keys, keys.len(), now, retry_timeout);
    let (next, listeners) = spec_drain_listener_keys(resumed, keys, keys.len());
    (next, callbacks + listeners)
}

pub open spec fn spec_drain_callbacks(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>)
    decreases count,
{
    if count == 0 {
        (map, Seq::empty())
    } else {
        let (prior, notes) = spec_drain_callbacks(map, id, (count - 1) as nat, now, retry_timeout);
        let obj = prior[id];
        let awaiter = obj.promise.callbacks[0];
        let since = match obj.promise.settled_at { Some(t) => t, None => 0 };
        let next = prior.insert(id, ObjV {
            promise: PromV { callbacks: obj.promise.callbacks.skip(1), ..obj.promise },
            ..obj
        });
        let (resumed, more) = spec_resume_offer(next, awaiter, id, since, now, retry_timeout);
        (resumed, notes + more)
    }
}

pub open spec fn spec_drain_settled_callbacks(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
    retry_timeout: u64,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
    if !map.contains_key(id) || map[id].promise.state == PromiseState::Pending {
        (map, Seq::empty())
    } else {
        spec_drain_callbacks(map, id, map[id].promise.callbacks.len(), now, retry_timeout)
    }
}

pub open spec fn spec_resume_offer(
    map: Map<Seq<char>, ObjV>,
    awaiter: Seq<char>,
    awaited: Seq<char>,
    since: Time,
    now: Time,
    retry_timeout: u64,
) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
    let resumed = spec_resume(map, awaiter, awaited, since, now);
    if map.contains_key(awaiter) {
        match spec_project_obj(map[awaiter], now).task {
            Some(task) if task.state == TaskState::Suspended => (
                resumed.insert(awaiter, spec_project_due_object(resumed[awaiter], now, retry_timeout)),
                seq![NoteV::Execute { id: awaiter, version: task.version }],
            ),
            _ => (resumed, Seq::empty()),
        }
    } else {
        (resumed, Seq::empty())
    }
}

pub open spec fn spec_project_due_object(
    obj: ObjV,
    now: Time,
    retry_timeout: u64,
) -> ObjV {
    if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
        spec_project_obj(obj, now)
    } else if obj.promise.state == PromiseState::Pending {
        match obj.task {
            Some(t) if t.state == TaskState::Acquired
                && match t.lease_timeout_at { Some(at) => at <= now, None => false } => {
                let task = spec_unlease(t, TaskState::Pending, Some(now));
                ObjV {
                    task: Some(TkV {
                        retry_timeout_at: Some(spec_sat_add(now, retry_timeout)),
                        ..task
                    }),
                    ..obj
                }
            },
            Some(t) if t.state == TaskState::Pending
                && match t.retry_timeout_at { Some(at) => at <= now, None => false } => {
                ObjV {
                    task: Some(TkV {
                        retry_timeout_at: Some(spec_sat_add(now, retry_timeout)),
                        ..t
                    }),
                    ..obj
                }
            },
            _ => obj,
        }
    } else {
        obj
    }
}

pub open spec fn spec_project_keys(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV>
    decreases count,
{
    if count == 0 {
        map
    } else {
        let prior = spec_project_keys(map, keys, (count - 1) as nat, now, retry_timeout);
        let id = keys[count as int - 1];
        if prior.contains_key(id) {
            prior.insert(id, spec_project_due_object(prior[id], now, retry_timeout))
        } else {
            prior
        }
    }
}

pub open spec fn spec_project_workflow(
    map: Map<Seq<char>, ObjV>,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV> {
    let keys = spec_sorted_present(map);
    spec_project_keys(map, keys, keys.len(), now, retry_timeout)
}

pub open spec fn spec_sweep(doc: DocumentBodyV, now: Time, retry_timeout: u64, limit: nat) -> (DocumentBodyV, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Workflow(objects) => {
            let (next, notes) = spec_bulk_workflow(objects, now, retry_timeout);
            (DocumentBodyV::Workflow(next), Seq::empty(), notes)
        },
        schedule => {
            let (next, _, born, notes) = spec_run_due(schedule, now, retry_timeout);
            (next, born, notes)
        },
    }
}

pub open spec fn spec_request_commits(
    doc: DocumentBodyV,
    request: Request,
    now: Time,
    retry_timeout: u64,
    limit: nat,
) -> bool {
    let (after, response, _, _) =
        spec_request_transition(doc, request, now, retry_timeout, limit);
    response != spec_unavailable(request) && after != doc
}

pub open spec fn spec_request_transition(
    doc: DocumentBodyV,
    request: Request,
    now: Time,
    retry_timeout: u64,
    limit: nat,
) -> (DocumentBodyV, Response, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Schedule(_) => {
            let (doc, response) = spec_handle(doc, request, now);
            (doc, response, Seq::empty(), Seq::empty())
        },
        DocumentBodyV::Workflow(objects) => {
            let (swept, notes) = spec_bulk_workflow(objects, now, retry_timeout);
            let (handled, response) = spec_handle(DocumentBodyV::Workflow(swept), request, now);
            (handled, response, Seq::empty(), notes)
        },
    }
}

pub open spec fn spec_occurrence(doc: DocumentBodyV, pending: PendingV, now: Time) -> DocumentBodyV {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if map.contains_key(pending.promise) || now < pending.at {
        doc
    } else {
        let timeout_at = spec_sat_add(pending.at, pending.timeout);
        let born = spec_new_obj(timeout_at, now, pending.param, pending.tags, spec_targeted(pending.tags) && !spec_timer(pending.tags));
        let promise = if timeout_at > pending.at {
            PromV { created_at: pending.at, ..born.promise }
        } else {
            born.promise
        };
        let task = match born.task {
            Some(t) if t.state == TaskState::Pending => Some(TkV { retry_timeout_at: Some(now), ..t }),
            other => other,
        };
        spec_with_workflow(doc, map.insert(pending.promise, ObjV { promise, task }))
    }
}

pub open spec fn spec_due_id(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time) -> Option<Seq<char>>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else if spec_obj_due(map[keys[0]], now) is Some { Some(keys[0]) }
    else { spec_due_id(map, keys.drop_first(), now) }
}

pub open spec fn spec_sorted_present(map: Map<Seq<char>, ObjV>) -> Seq<Seq<char>> {
    spec_sorted(map.dom())
}

#[verifier::opaque]
pub open spec fn spec_min_key(keys: Set<Seq<char>>) -> Seq<char> {
    choose|k: Seq<char>| keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

pub(crate) open spec fn least_key(keys: Set<Seq<char>>, k: Seq<char>) -> bool {
    keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

pub open spec fn spec_sorted(keys: Set<Seq<char>>) -> Seq<Seq<char>>
    decreases keys.len(),
    via spec_sorted_decreases
{
    if !keys.finite() || keys.len() == 0 { Seq::empty() }
    else {
        let k = spec_min_key(keys);
        seq![k] + spec_sorted(keys.remove(k))
    }
}

pub open spec fn spec_earlier(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

pub open spec fn spec_promise_due(obj: ObjV, now: Time) -> Option<u64> {
    if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
        Some(obj.promise.timeout_at)
    } else if obj.promise.state != PromiseState::Pending
        && (obj.promise.callbacks.len() > 0 || obj.promise.listeners.len() > 0)
    {
        let at = match obj.promise.settled_at { Some(t) => t, None => 0 };
        if at <= now { Some(at) } else { None }
    } else {
        None
    }
}

pub open spec fn spec_lease_due(obj: ObjV, now: Time) -> Option<u64> {
    match obj.task {
        Some(t) if obj.promise.state == PromiseState::Pending && t.state == TaskState::Acquired => match t.lease_timeout_at {
            Some(at) if at <= now => Some(at),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn spec_retry_due(obj: ObjV, now: Time) -> Option<u64> {
    match obj.task {
        Some(t) if obj.promise.state == PromiseState::Pending && t.state == TaskState::Pending => match t.retry_timeout_at {
            Some(at) if at <= now => Some(at),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn spec_obj_due(obj: ObjV, now: Time) -> Option<u64> {
    spec_earlier(spec_earlier(spec_promise_due(obj, now), spec_lease_due(obj, now)), spec_retry_due(obj, now))
}

pub open spec fn spec_step_object(map: Map<Seq<char>, ObjV>, id: Seq<char>, now: Time, retry_timeout: u64) -> (Map<Seq<char>, ObjV>, Seq<NoteV>) {
    if !map.contains_key(id) {
        (map, Seq::empty())
    } else {
        let obj = map[id];
        if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
            (map.insert(id, spec_project_obj(obj, now)), Seq::empty())
        } else if obj.promise.state == PromiseState::Pending {
            match obj.task {
                Some(t) if t.state == TaskState::Acquired && match t.lease_timeout_at { Some(at) => at <= now, None => false } => {
                    let obj = ObjV { task: Some(spec_unlease(t, TaskState::Pending, Some(now))), ..obj };
                    (map.insert(id, obj), Seq::empty())
                },
                Some(t) if t.state == TaskState::Pending && match t.retry_timeout_at { Some(at) => at <= now, None => false } => {
                    let obj = ObjV { task: Some(TkV { retry_timeout_at: Some(spec_sat_add(now, retry_timeout)), ..t }), ..obj };
                    (map.insert(id, obj), seq![NoteV::Execute { id, version: t.version }])
                },
                _ => (map, Seq::empty()),
            }
        } else if obj.promise.callbacks.len() > 0 {
            let awaiter = obj.promise.callbacks[0];
            let since = match obj.promise.settled_at { Some(t) => t, None => 0 };
            let obj = ObjV { promise: PromV { callbacks: obj.promise.callbacks.skip(1), ..obj.promise }, ..obj };
            let map = map.insert(id, obj);
            (spec_resume(map, awaiter, id, since, now), Seq::empty())
        } else if obj.promise.listeners.len() > 0 {
            let address = obj.promise.listeners[0];
            let promise = spec_record(spec_string(id), obj.promise);
            let obj = ObjV { promise: PromV { listeners: obj.promise.listeners.skip(1), ..obj.promise }, ..obj };
            (map.insert(id, obj), seq![NoteV::Unblock { address, promise }])
        } else {
            (map, Seq::empty())
        }
    }
}

pub open spec fn spec_resume(map: Map<Seq<char>, ObjV>, awaiter: Seq<char>, awaited: Seq<char>, since: Time, now: Time) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(awaiter) {
        map
    } else {
        match spec_project_obj(map[awaiter], now).task {
            None => map,
            Some(t) => match t.state {
                TaskState::Suspended => map.insert(awaiter, ObjV {
                    task: Some(TkV {
                        state: TaskState::Pending,
                        pid: None,
                        ttl: None,
                        lease_timeout_at: None,
                        retry_timeout_at: Some(now),
                        resumes: seq![awaited],
                        ..t
                    }),
                    ..map[awaiter]
                }),
                TaskState::Fulfilled => map,
                _ => if t.resumes.contains(awaited) {
                    map
                } else {
                    map.insert(awaiter, ObjV { task: Some(TkV { resumes: t.resumes.push(awaited), ..t }), ..map[awaiter] })
                },
            },
        }
    }
}

pub open spec fn spec_wake(node: NodeV) -> Option<nat> {
    if node.flight is Some { None } else { spec_next(node) }
}

pub open spec fn spec_next(node: NodeV) -> Option<nat> {
    let from_pending = if node.pending.len() == 0 { None } else { Some(node.pending[0].at as nat) };
    spec_min_nat(from_pending, spec_deadlines(node, node.documents, 0))
}

pub open spec fn spec_min_nat(a: Option<nat>, b: Option<nat>) -> Option<nat> {
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

pub open spec fn spec_deadlines(node: NodeV, docs: Seq<CachedV>, i: int) -> Option<nat>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        None
    } else if !spec_owns(node, docs[i].key) {
        spec_deadlines(node, docs, i + 1)
    } else {
        spec_min_nat(spec_body_deadline(spec_read(docs[i].key, docs[i].body)), spec_deadlines(node, docs, i + 1))
    }
}

pub open spec fn spec_body_deadline(doc: DocumentBodyV) -> Option<nat> {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) => match schedule.next_run_at {
            Some(at) => Some(at as nat),
            None => None,
        },
        DocumentBodyV::Workflow(map) => spec_map_deadline(map, spec_sorted(map.dom())),
        DocumentBodyV::Schedule(None) => None,
    }
}

pub open spec fn spec_map_deadline(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>) -> Option<nat>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else { spec_min_nat(spec_obj_deadline(map[keys[0]]), spec_map_deadline(map, keys.drop_first())) }
}

pub open spec fn spec_obj_deadline(obj: ObjV) -> Option<nat> {
    match spec_obj_due(obj, u64::MAX) {
        Some(at) => Some(at as nat),
        None => None,
    }
}

pub open spec fn spec_earliest_key(node: NodeV, now: Time) -> Option<Seq<char>> {
    spec_earliest_from(node, node.documents, 0, now, None)
}

pub open spec fn spec_earliest_from(node: NodeV, docs: Seq<CachedV>, i: int, now: Time, best: Option<(u64, Seq<char>)>) -> Option<Seq<char>>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        match best { Some((_, key)) => Some(key), None => None }
    } else if !spec_owns(node, docs[i].key) {
        spec_earliest_from(node, docs, i + 1, now, best)
    } else {
        match spec_earliest_in(spec_read(docs[i].key, docs[i].body), now) {
            Some(at) => {
                let better = match best { None => true, Some((b, _)) => at < b };
                let best = if better { Some((at, docs[i].key)) } else { best };
                spec_earliest_from(node, docs, i + 1, now, best)
            },
            None => spec_earliest_from(node, docs, i + 1, now, best),
        }
    }
}

pub open spec fn spec_earliest_in(doc: DocumentBodyV, now: Time) -> Option<u64> {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.next_run_at.is_some() && schedule.next_run_at.unwrap() <= now => schedule.next_run_at,
        DocumentBodyV::Workflow(map) => spec_map_due(map, spec_sorted(map.dom()), now),
        _ => None,
    }
}

pub open spec fn spec_map_due(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time) -> Option<u64>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else { spec_earlier(spec_obj_due(map[keys[0]], now), spec_map_due(map, keys.drop_first(), now)) }
}

pub open spec fn spec_wrap_mul(a: u64, b: u64) -> u64 {
    (((a as nat) * (b as nat)) % 0x10000000000000000) as u64
}

pub open spec fn spec_fnv_acc(bytes: Seq<u8>, h: u64) -> u64
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        h
    } else {
        let mixed = h ^ (bytes[0] as u64);
        spec_fnv_acc(bytes.drop_first(), spec_wrap_mul(mixed, 0x00000100000001b3))
    }
}

pub open spec fn spec_utf8(chars: Seq<char>) -> Seq<u8>
    decreases chars.len(),
{
    if chars.len() == 0 {
        Seq::empty()
    } else {
        let c = chars[0] as u64;
        let head = if c < 0x80 {
            seq![c as u8]
        } else if c < 0x800 {
            seq![((c >> 6) | 0xc0) as u8, ((c & 0x3f) | 0x80) as u8]
        } else if c < 0x10000 {
            seq![((c >> 12) | 0xe0) as u8, (((c >> 6) & 0x3f) | 0x80) as u8, ((c & 0x3f) | 0x80) as u8]
        } else {
            seq![
                ((c >> 18) | 0xf0) as u8,
                (((c >> 12) & 0x3f) | 0x80) as u8,
                (((c >> 6) & 0x3f) | 0x80) as u8,
                ((c & 0x3f) | 0x80) as u8,
            ]
        };
        head + spec_utf8(chars.drop_first())
    }
}

pub open spec fn spec_fnv(chars: Seq<char>) -> u64 {
    spec_fnv_acc(spec_utf8(chars), 0xcbf29ce484222325)
}

pub open spec fn spec_hex_digit(n: u64) -> char {
    if n == 0 { '0' }
    else if n == 1 { '1' }
    else if n == 2 { '2' }
    else if n == 3 { '3' }
    else if n == 4 { '4' }
    else if n == 5 { '5' }
    else if n == 6 { '6' }
    else if n == 7 { '7' }
    else if n == 8 { '8' }
    else if n == 9 { '9' }
    else if n == 10 { 'a' }
    else if n == 11 { 'b' }
    else if n == 12 { 'c' }
    else if n == 13 { 'd' }
    else if n == 14 { 'e' }
    else { 'f' }
}

pub open spec fn spec_hex_from(n: u64, shift: int) -> Seq<char>
    decreases shift,
{
    let d = (n >> (shift * 4)) & 0xf;
    if shift <= 0 {
        seq![spec_hex_digit(d)]
    } else {
        seq![spec_hex_digit(d)] + spec_hex_from(n, shift - 1)
    }
}

pub open spec fn spec_etag_chars(body: Seq<u8>) -> Seq<char> {
    spec_hex_from(spec_fnv_acc(spec_lossy(body), 0xcbf29ce484222325), 15)
}

pub open spec fn spec_cont(b: u8) -> bool {
    b >= 0x80 && b < 0xc0
}

pub open spec fn spec_utf8_width(lead: u8) -> nat {
    if lead < 0x80 {
        1
    } else if lead >= 0xc2 && lead <= 0xdf {
        2
    } else if lead >= 0xe0 && lead <= 0xef {
        3
    } else if lead >= 0xf0 && lead <= 0xf4 {
        4
    } else {
        0
    }
}

pub open spec fn spec_utf8_ok(lead: u8, pos: nat, b: u8) -> bool {
    if pos == 0 {
        true
    } else if pos == 1 {
        if lead >= 0xc2 && lead <= 0xdf {
            spec_cont(b)
        } else if lead == 0xe0 {
            b >= 0xa0 && b <= 0xbf
        } else if (lead >= 0xe1 && lead <= 0xec) || (lead >= 0xee && lead <= 0xef) {
            spec_cont(b)
        } else if lead == 0xed {
            b >= 0x80 && b <= 0x9f
        } else if lead == 0xf0 {
            b >= 0x90 && b <= 0xbf
        } else if lead >= 0xf1 && lead <= 0xf3 {
            spec_cont(b)
        } else if lead == 0xf4 {
            b >= 0x80 && b <= 0x8f
        } else {
            false
        }
    } else {
        spec_cont(b)
    }
}

pub open spec fn spec_prefix(bytes: Seq<u8>, width: nat, pos: nat) -> nat
    decreases width - pos,
{
    if pos >= width {
        width
    } else if pos >= bytes.len() || !spec_utf8_ok(bytes[0], pos, bytes[pos as int]) {
        pos
    } else {
        spec_prefix(bytes, width, pos + 1)
    }
}

pub open spec fn spec_lossy(bytes: Seq<u8>) -> Seq<u8>
    decreases bytes.len(),
    via spec_lossy_decreases
{
    if bytes.len() == 0 {
        Seq::empty()
    } else {
        let width = spec_utf8_width(bytes[0]);
        if width == 1 {
            seq![bytes[0]] + spec_lossy(bytes.skip(1))
        } else if width == 0 {
            seq![0xefu8, 0xbfu8, 0xbdu8] + spec_lossy(bytes.skip(1))
        } else {
            let prefix = spec_prefix(bytes, width, 1);
            if prefix == width {
                bytes.take(width as int) + spec_lossy(bytes.skip(width as int))
            } else {
                seq![0xefu8, 0xbfu8, 0xbdu8] + spec_lossy(bytes.skip(prefix as int))
            }
        }
    }
}

pub open spec fn spec_sat_add(a: u64, b: u64) -> u64 {
    if (a as nat) + (b as nat) > (u64::MAX as nat) {
        u64::MAX
    } else {
        ((a as nat) + (b as nat)) as u64
    }
}

pub open spec fn spec_etag(body: Seq<u8>) -> Etag {
    Etag(spec_string(spec_etag_chars(body)))
}

pub open spec fn spec_find(entries: Seq<EntryV>, key: Seq<char>, i: int) -> Option<int>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() {
        None
    } else if entries[i].key == key {
        Some(i)
    } else {
        spec_find(entries, key, i + 1)
    }
}

pub open spec fn spec_insert_at(entries: Seq<EntryV>, entry: EntryV, i: int) -> Seq<EntryV>
    decreases entries.len() - i,
{
    if i >= entries.len() {
        entries.push(entry)
    } else if spec_before(entry.key, entries[i].key) {
        entries.take(i).push(entry) + entries.skip(i)
    } else {
        spec_insert_at(entries, entry, i + 1)
    }
}

pub open spec fn spec_before(a: Seq<char>, b: Seq<char>) -> bool
    decreases a.len() + b.len(),
{
    if a.len() == 0 { b.len() != 0 }
    else if b.len() == 0 { false }
    else if a[0] != b[0] { a[0] < b[0] }
    else { spec_before(a.drop_first(), b.drop_first()) }
}

pub open spec fn spec_put(entries: Seq<EntryV>, entry: EntryV) -> Seq<EntryV> {
    match spec_find(entries, entry.key, 0) {
        Some(i) => entries.update(i, entry),
        None => spec_insert_at(entries, entry, 0),
    }
}

pub open spec fn spec_remove_at(entries: Seq<EntryV>, i: int) -> Seq<EntryV> {
    entries.take(i) + entries.skip(i + 1)
}

pub open spec fn spec_bump(version: nat) -> nat {
    if version < u64::MAX as nat { version + 1 } else { version }
}

pub open spec fn spec_apply(store: StoreV, req: StoreReq) -> (StoreV, StoreRes) {
    match req {
        StoreReq::Get { key } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreRes::Get { result: Ok(None) }),
                Some(i) => {
                    let body = store.entries[i].body;
                    (store, StoreRes::Get { result: Ok(Some((spec_bytes(body), spec_etag(body)))) })
                },
            }
        },
        StoreReq::GetIfNoneMatch { key, etag } => {
            match spec_find(store.entries, key@, 0) {
                None => (store, StoreRes::GetIfNoneMatch { result: Ok(Read::Absent) }),
                Some(i) => {
                    let body = store.entries[i].body;
                    let have = spec_etag(body);
                    if have == etag {
                        (store, StoreRes::GetIfNoneMatch { result: Ok(Read::NotModified) })
                    } else {
                        (store, StoreRes::GetIfNoneMatch { result: Ok(Read::Body(spec_bytes(body), have)) })
                    }
                },
            }
        },
        StoreReq::PutIfNoneMatch { key, body } => {
            if spec_find(store.entries, key@, 0) is Some {
                (store, StoreRes::PutIfNoneMatch { result: Err(StoreError::PreconditionFailed) })
            } else {
                let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version: 1 });
                (StoreV { entries, ..store }, StoreRes::PutIfNoneMatch { result: Ok(spec_etag(body@)) })
            }
        },
        StoreReq::PutIfMatch { key, body, etag } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) if spec_etag(store.entries[i].body) == etag => {
                    let version = spec_bump(store.entries[i].version);
                    let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
                    (StoreV { entries, ..store }, StoreRes::PutIfMatch { result: Ok(spec_etag(body@)) })
                },
                _ => (store, StoreRes::PutIfMatch { result: Err(StoreError::PreconditionFailed) }),
            }
        },
        StoreReq::AppIfMatch { key, offset, body, etag } => {
            if !store.appendable {
                (store, StoreRes::AppIfMatch {
                    result: Err(StoreError::Unavailable(spec_string(seq![
                        't', 'h', 'i', 's', ' ', 's', 't', 'o', 'r', 'e', ' ', 'd', 'o', 'e', 's', ' ',
                        'n', 'o', 't', ' ', 'a', 'p', 'p', 'e', 'n', 'd',
                    ]))),
                })
            } else {
                match spec_find(store.entries, key@, 0) {
                    Some(i) if spec_etag(store.entries[i].body) == etag && store.entries[i].body.len() == offset => {
                        let joined = store.entries[i].body + body@;
                        let version = spec_bump(store.entries[i].version);
                        let entries = spec_put(store.entries, EntryV { key: key@, body: joined, version });
                        (StoreV { entries, ..store }, StoreRes::AppIfMatch { result: Ok(spec_etag(joined)) })
                    },
                    _ => (store, StoreRes::AppIfMatch { result: Err(StoreError::PreconditionFailed) }),
                }
            }
        },
        StoreReq::Put { key, body } => {
            let version = match spec_find(store.entries, key@, 0) {
                Some(i) => spec_bump(store.entries[i].version),
                None => 1,
            };
            let entries = spec_put(store.entries, EntryV { key: key@, body: body@, version });
            (StoreV { entries, ..store }, StoreRes::Put { result: Ok(()) })
        },
        StoreReq::Del { key } => {
            match spec_find(store.entries, key@, 0) {
                Some(i) => (StoreV { entries: spec_remove_at(store.entries, i), ..store }, StoreRes::Del { result: Ok(()) }),
                None => (store, StoreRes::Del { result: Ok(()) }),
            }
        },
        StoreReq::List { prefix, max_keys } => {
            (store, StoreRes::List { result: Ok(spec_bytes_keys(spec_list(store.entries, prefix@, max_keys as nat, 0, Seq::empty()))) })
        },
        StoreReq::ListPrefixes { prefix } => {
            (store, StoreRes::ListPrefixes { result: Ok(spec_bytes_keys(spec_prefixes(store.entries, prefix@, 0, Seq::empty()))) })
        },
    }
}

pub open spec fn spec_list(entries: Seq<EntryV>, prefix: Seq<char>, max: nat, i: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() || acc.len() >= max {
        acc
    } else if spec_starts(entries[i].key, prefix) {
        spec_list(entries, prefix, max, i + 1, acc.push(entries[i].key))
    } else {
        spec_list(entries, prefix, max, i + 1, acc)
    }
}

pub open spec fn spec_starts(text: Seq<char>, prefix: Seq<char>) -> bool
    decreases prefix.len(),
{
    if prefix.len() == 0 { true }
    else if text.len() == 0 { false }
    else { text[0] == prefix[0] && spec_starts(text.drop_first(), prefix.drop_first()) }
}

pub open spec fn spec_prefixes(entries: Seq<EntryV>, prefix: Seq<char>, i: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases entries.len() - i,
{
    if i < 0 || i >= entries.len() {
        acc
    } else if spec_starts(entries[i].key, prefix) {
        let tail = entries[i].key.skip(prefix.len() as int);
        match spec_slash(tail, 0) {
            Some(n) => {
                let child = entries[i].key.take(prefix.len() + n + 1);
                let acc = if acc.len() > 0 && acc.last() == child { acc } else { acc.push(child) };
                spec_prefixes(entries, prefix, i + 1, acc)
            },
            None => spec_prefixes(entries, prefix, i + 1, acc),
        }
    } else {
        spec_prefixes(entries, prefix, i + 1, acc)
    }
}

pub open spec fn spec_slash(text: Seq<char>, i: int) -> Option<int>
    decreases text.len() - i,
{
    if i < 0 || i >= text.len() { None }
    else if text[i] == '/' { Some(i) }
    else { spec_slash(text, i + 1) }
}

pub open spec fn spec_bytes_keys(keys: Seq<Seq<char>>) -> Vec<String> {
    choose|v: Vec<String>| v@.map_values(|s: String| s@) == keys
}

pub open spec fn key_views(v: Seq<String>) -> Seq<Seq<char>> {
    v.map_values(|s: String| s@)
}
}
