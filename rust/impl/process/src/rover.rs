//! Rover adapter for the production process.
//!
//! The node transition is not reimplemented here. A [`Node`] owns the real
//! [`crate::State`], clones it to form Rover's next branch, and invokes
//! [`crate::State::on_event`]. The adapter only supplies the runtime shell:
//! store envelopes, one replaceable wake, pending client calls, and projection
//! of replies and worker sends to the shared abstract boundary.

use vstd::prelude::*;

use echod_abstract::{BoundaryEvent, Call as BoundaryCall, Dispatch, Output};
use echod_concrete::model::Pid;
use echod_concrete::store::{Store, StoreReq, StoreRes, StoreV};
use echod_rover::certificate::trusted::copy;
use echod_rover::rover::{Process, ProcessEvent, RoverModel, StepResult};
use echod_rover::Time;
use echod_types::{origin_of, Request};

use crate::target::Target;
use crate::types::{Answer, Armed, Call, Effect, Event, Message as ProcessMessage, RequestEvent};
use crate::{Config, State};

#[cfg(verus_keep_ghost)]
use crate::config::ConfigSpec;
#[cfg(verus_keep_ghost)]
use crate::handler::spec_on_event;
#[cfg(verus_keep_ghost)]
use crate::state::StateSpec;
#[cfg(verus_keep_ghost)]
use crate::target::TargetSpec;
#[cfg(verus_keep_ghost)]
use crate::types::{AnswerSpec, EffectSpec, EventSpec, MessageSpec, RequestEventSpec};
#[cfg(verus_keep_ghost)]
use echod_concrete::store::{spec_apply, StoreReqSpec};
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::{Label, StepResultV, StepResultV as RoverStepV};
#[cfg(verus_keep_ghost)]
use echod_types::Response;

verus! {

/// The production model has one node and the store used by the runtime.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Model;

/// Network messages. `Request`, `Reply`, and `Send` are the only boundary
/// variants. Store traffic is internal.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Request(BoundaryCall),
    Reply(Output),
    Send(Output),
    StoreReq { op: u64, request: StoreReq },
    StoreRes { op: u64, response: StoreRes },
}

/// Runtime-shell state around the production core.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Node {
    pub core: State,
    /// Calls accepted at the boundary and not answered yet.
    pub pending: Vec<(u64, BoundaryCall)>,
    /// The currently armed replacement wake.
    pub wake: Option<(Time, Armed)>,
    #[cfg(verus_keep_ghost)]
    pub store_certificates: Ghost<
        Map<u64, crate::global_store_invariants::StoreEffectCertificateV>,
    >,
}

/// The adapter's local states.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Local {
    Node(Node),
    Store(Store),
}

/// Specification view of [`Node`]. In ordinary Rust the proof-only core field
/// is erased; Verus sees the production [`StateSpec`] itself.
pub struct NodeV {
    #[cfg(verus_keep_ghost)]
    pub core: StateSpec,
    pub pending: Seq<(u64, BoundaryCall)>,
    pub wake: Option<(Time, Armed)>,
    #[cfg(verus_keep_ghost)]
    pub store_certificates:
        Map<u64, crate::global_store_invariants::StoreEffectCertificateV>,
}

pub enum LocalV {
    Node(NodeV),
    Store(StoreV),
}

impl View for Node {
    type V = NodeV;

    open spec fn view(&self) -> NodeV {
        NodeV {
            core: self.core.deep_view(),
            pending: self.pending@,
            wake: self.wake,
            #[cfg(verus_keep_ghost)]
            store_certificates: self.store_certificates@,
        }
    }
}

impl View for Local {
    type V = LocalV;

    open spec fn view(&self) -> LocalV {
        match self {
            Local::Node(node) => LocalV::Node(node@),
            Local::Store(store) => LocalV::Store(store@),
        }
    }
}

/// The document selected by the admitted protocol request.
pub open spec fn spec_target(request: Request) -> Option<TargetSpec> {
    match request {
        Request::PromiseGet(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::PromiseCreate(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::PromiseSettle(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::PromiseRegisterCallback(q) => Some(TargetSpec::Origin(echod_types::origin(q.awaited@))),
        Request::PromiseRegisterListener(q) => Some(TargetSpec::Origin(echod_types::origin(q.awaited@))),
        Request::TaskGet(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskCreate(q) => Some(TargetSpec::Origin(echod_types::origin(q.action.id@))),
        Request::TaskAcquire(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskFulfill(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskRelease(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskHalt(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskContinue(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskFence(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskFenceCheck(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskSuspend(q) => Some(TargetSpec::Origin(echod_types::origin(q.id@))),
        Request::TaskHeartbeat(q) => if q.tasks@.len() == 0 {
            None
        } else {
            Some(TargetSpec::Origin(echod_types::origin(q.tasks@[0].id@)))
        },
        Request::ScheduleGet(q) => Some(TargetSpec::Schedule(q.id@)),
        Request::ScheduleCreate(q) => Some(TargetSpec::Schedule(q.id@)),
        Request::ScheduleDelete(q) => Some(TargetSpec::Schedule(q.id@)),
    }
}

pub open spec fn spec_empty_heartbeat(request: Request) -> bool {
    match request {
        Request::TaskHeartbeat(q) => q.tasks@.len() == 0,
        _ => false,
    }
}

pub fn empty_heartbeat(request: &Request) -> (result: bool)
    ensures
        result == spec_empty_heartbeat(*request),
{
    match request {
        Request::TaskHeartbeat(q) => q.tasks.is_empty(),
        _ => false,
    }
}

fn origin_target(id: &String) -> (result: Target)
    ensures
        result.deep_view() == TargetSpec::Origin(echod_types::origin(id@)),
{
    Target::Origin(crate::verified::text::text(origin_of(id.as_str())))
}

/// Executable admission projection. This is the same routing split as
/// [`spec_target`].
pub fn target(request: &Request) -> (result: Option<Target>)
    ensures
        result.deep_view() == spec_target(*request),
{
    match request {
        Request::PromiseGet(q) => Some(origin_target(&q.id)),
        Request::PromiseCreate(q) => Some(origin_target(&q.id)),
        Request::PromiseSettle(q) => Some(origin_target(&q.id)),
        Request::PromiseRegisterCallback(q) => Some(origin_target(&q.awaited)),
        Request::PromiseRegisterListener(q) => Some(origin_target(&q.awaited)),
        Request::TaskGet(q) => Some(origin_target(&q.id)),
        Request::TaskCreate(q) => Some(origin_target(&q.action.id)),
        Request::TaskAcquire(q) => Some(origin_target(&q.id)),
        Request::TaskFulfill(q) => Some(origin_target(&q.id)),
        Request::TaskRelease(q) => Some(origin_target(&q.id)),
        Request::TaskHalt(q) => Some(origin_target(&q.id)),
        Request::TaskContinue(q) => Some(origin_target(&q.id)),
        Request::TaskFence(q) => Some(origin_target(&q.id)),
        Request::TaskFenceCheck(q) => Some(origin_target(&q.id)),
        Request::TaskSuspend(q) => Some(origin_target(&q.id)),
        Request::TaskHeartbeat(q) => {
            if q.tasks.is_empty() { None } else { Some(origin_target(&q.tasks[0].id)) }
        }
        Request::ScheduleGet(q) => Some(Target::Schedule(copy(&q.id))),
        Request::ScheduleCreate(q) => Some(Target::Schedule(copy(&q.id))),
        Request::ScheduleDelete(q) => Some(Target::Schedule(copy(&q.id))),
    }
}

pub open spec fn spec_call(call: BoundaryCall, target: TargetSpec, now: Time) -> crate::types::CallSpec {
    crate::types::CallSpec {
        id: call.id,
        kind: Seq::empty(),
        corr: call.client@,
        target,
        request: call.request,
        action_kind: None,
        now,
        pinned: false,
    }
}

fn process_call(call: &BoundaryCall, target: Target, now: Time) -> (result: Call)
    ensures
        result.deep_view() == spec_call(*call, target.deep_view(), now),
{
    Call {
        id: call.id,
        kind: String::new(),
        corr: copy(&call.client),
        target,
        request: copy(&call.request),
        action_kind: None,
        now,
        pinned: false,
    }
}

pub open spec fn spec_pending_remove(
    pending: Seq<(u64, BoundaryCall)>,
    id: u64,
) -> Seq<(u64, BoundaryCall)> {
    spec_take_pending(pending, id).1
}

pub open spec fn spec_take_pending(
    pending: Seq<(u64, BoundaryCall)>,
    id: u64,
) -> (Option<BoundaryCall>, Seq<(u64, BoundaryCall)>)
    decreases pending.len(),
{
    if pending.len() == 0 {
        (None, Seq::empty())
    } else {
        let last = pending.last();
        let (found, kept) = spec_take_pending(pending.drop_last(), id);
        if last.0 == id {
            (if found is Some { found } else { Some(last.1) }, kept)
        } else {
            (found, kept.push(last))
        }
    }
}

fn remove_pending(
    pending: &mut Vec<(u64, BoundaryCall)>,
    id: u64,
) -> (result: Option<BoundaryCall>)
    ensures
        (result, final(pending)@) == spec_take_pending(old(pending)@, id),
    decreases old(pending).len(),
{
    match pending.pop() {
        None => None,
        Some(last) => {
            let found = remove_pending(pending, id);
            if last.0 == id {
                if found.is_some() { found } else { Some(last.1) }
            } else {
                pending.push(last);
                found
            }
        }
    }
}

pub open spec fn spec_dispatch(
    address: Seq<char>,
    message: MessageSpec,
) -> Dispatch {
    match message {
        MessageSpec::Execute { task_id, version } => {
            Dispatch::Execute {
                id: echod_concrete::model::spec_string(task_id),
                version,
            }
        }
        MessageSpec::Unblock(promise) => {
            Dispatch::Unblock {
                address: echod_concrete::model::spec_string(address),
                promise,
            }
        }
    }
}

pub open spec fn spec_store_request(request: StoreReqSpec) -> StoreReq {
    choose|result: StoreReq| result.deep_view() == request
}

pub open spec fn store_request_bounded(request: StoreReqSpec) -> bool {
    crate::state::spec_store_request_representable(request)
}

pub proof fn lemma_store_request_bounded(request: StoreReq)
    ensures
        store_request_bounded(request.deep_view()),
{
    crate::state::lemma_store_request_representable(&request);
}

pub proof fn lemma_store_request_realised(request: StoreReqSpec)
    requires
        store_request_bounded(request),
    ensures
        spec_store_request(request).deep_view() == request,
{
    match request {
        StoreReqSpec::Get { key } => {
            echod_abstract::trusted::axiom_string_realised(key);
            let text = choose|text: String| text@ == key;
            assert(StoreReq::Get { key: text }.deep_view() == request);
        }
        StoreReqSpec::GetIfNoneMatch { key, etag } => {
            echod_abstract::trusted::axiom_string_realised(key);
            echod_abstract::trusted::axiom_string_realised(etag.0);
            let text = choose|text: String| text@ == key;
            let tag = choose|tag: String| tag@ == etag.0;
            assert(StoreReq::GetIfNoneMatch {
                key: text,
                etag: echod_concrete::Etag(tag),
            }.deep_view() == request);
        }
        StoreReqSpec::PutIfMatch { key, body, etag } => {
            echod_abstract::trusted::axiom_string_realised(key);
            echod_abstract::trusted::axiom_bytes_realised(body);
            echod_abstract::trusted::axiom_string_realised(etag.0);
            let text = choose|text: String| text@ == key;
            let bytes = choose|bytes: Vec<u8>| bytes@ == body;
            let tag = choose|tag: String| tag@ == etag.0;
            assert(StoreReq::PutIfMatch {
                key: text,
                body: bytes,
                etag: echod_concrete::Etag(tag),
            }.deep_view() == request);
        }
        StoreReqSpec::PutIfNoneMatch { key, body } => {
            echod_abstract::trusted::axiom_string_realised(key);
            echod_abstract::trusted::axiom_bytes_realised(body);
            let text = choose|text: String| text@ == key;
            let bytes = choose|bytes: Vec<u8>| bytes@ == body;
            assert(StoreReq::PutIfNoneMatch {
                key: text,
                body: bytes,
            }.deep_view() == request);
        }
        StoreReqSpec::AppIfMatch { key, offset, body, etag } => {
            echod_abstract::trusted::axiom_string_realised(key);
            echod_abstract::trusted::axiom_bytes_realised(body);
            echod_abstract::trusted::axiom_string_realised(etag.0);
            let text = choose|text: String| text@ == key;
            let bytes = choose|bytes: Vec<u8>| bytes@ == body;
            let tag = choose|tag: String| tag@ == etag.0;
            assert(StoreReq::AppIfMatch {
                key: text,
                offset,
                body: bytes,
                etag: echod_concrete::Etag(tag),
            }.deep_view() == request);
        }
        StoreReqSpec::Put { key, body } => {
            echod_abstract::trusted::axiom_string_realised(key);
            echod_abstract::trusted::axiom_bytes_realised(body);
            let text = choose|text: String| text@ == key;
            let bytes = choose|bytes: Vec<u8>| bytes@ == body;
            assert(StoreReq::Put {
                key: text,
                body: bytes,
            }.deep_view() == request);
        }
        StoreReqSpec::Del { key } => {
            echod_abstract::trusted::axiom_string_realised(key);
            let text = choose|text: String| text@ == key;
            assert(StoreReq::Del { key: text }.deep_view() == request);
        }
        StoreReqSpec::List { prefix, max_keys } => {
            echod_abstract::trusted::axiom_string_realised(prefix);
            let text = choose|text: String| text@ == prefix;
            assert(StoreReq::List {
                prefix: text,
                max_keys,
            }.deep_view() == request);
        }
        StoreReqSpec::ListPrefixes { prefix } => {
            echod_abstract::trusted::axiom_string_realised(prefix);
            let text = choose|text: String| text@ == prefix;
            assert(StoreReq::ListPrefixes {
                prefix: text,
            }.deep_view() == request);
        }
    }
}

pub proof fn lemma_store_request_ext(left: StoreReq, right: StoreReq)
    requires
        left.deep_view() == right.deep_view(),
    ensures
        left == right,
{
    match (left, right) {
        (StoreReq::Get { key: a }, StoreReq::Get { key: b }) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
        }
        (
            StoreReq::GetIfNoneMatch { key: a, etag: ea },
            StoreReq::GetIfNoneMatch { key: b, etag: eb },
        ) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
            echod_abstract::trusted::axiom_string_ext(ea.0, eb.0);
        }
        (
            StoreReq::PutIfMatch { key: a, body: ba, etag: ea },
            StoreReq::PutIfMatch { key: b, body: bb, etag: eb },
        ) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
            echod_abstract::trusted::axiom_vec_ext(ba, bb);
            echod_abstract::trusted::axiom_string_ext(ea.0, eb.0);
        }
        (
            StoreReq::PutIfNoneMatch { key: a, body: ba },
            StoreReq::PutIfNoneMatch { key: b, body: bb },
        ) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
            echod_abstract::trusted::axiom_vec_ext(ba, bb);
        }
        (
            StoreReq::AppIfMatch {
                key: a,
                body: ba,
                etag: ea,
                ..
            },
            StoreReq::AppIfMatch {
                key: b,
                body: bb,
                etag: eb,
                ..
            },
        ) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
            echod_abstract::trusted::axiom_vec_ext(ba, bb);
            echod_abstract::trusted::axiom_string_ext(ea.0, eb.0);
        }
        (
            StoreReq::Put { key: a, body: ba },
            StoreReq::Put { key: b, body: bb },
        ) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
            echod_abstract::trusted::axiom_vec_ext(ba, bb);
        }
        (StoreReq::Del { key: a }, StoreReq::Del { key: b }) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
        }
        (
            StoreReq::List { prefix: a, .. },
            StoreReq::List { prefix: b, .. },
        ) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
        }
        (
            StoreReq::ListPrefixes { prefix: a },
            StoreReq::ListPrefixes { prefix: b },
        ) => {
            echod_abstract::trusted::axiom_string_ext(a, b);
        }
        _ => {}
    }
}

fn dispatch(address: String, message: ProcessMessage) -> (result: Dispatch)
    ensures
        result == spec_dispatch(address@, message.deep_view()),
{
    match message {
        ProcessMessage::Execute { task_id, version } => {
            proof {
                echod_concrete::interpret::lemma_string_of(task_id);
            }
            Dispatch::Execute { id: task_id, version }
        }
        ProcessMessage::Unblock(promise) => {
            proof {
                echod_concrete::interpret::lemma_string_of(address);
            }
            Dispatch::Unblock { address, promise }
        }
    }
}

/// Interpret exactly the effects returned by the production transition.
fn apply_effects(
    node: &mut Node,
    now: Time,
    mut effects: Vec<Effect>,
) -> (send: Vec<(Pid, Message)>)
    ensures
        (final(node)@, send@)
            == spec_effects(old(node)@, now, effects.deep_view()),
    decreases effects.len(),
{
    let ghost before_node = node@;
    let ghost all = effects.deep_view();
    reveal(spec_effects);
    match effects.pop() {
        None => {
            assert(all.len() == 0);
            assert((node@, Seq::<(Pid, Message)>::empty())
                == spec_effects(before_node, now, all));
            Vec::new()
        }
        Some(effect) => {
            assert(effects.deep_view() == all.drop_last());
            assert(effect.deep_view() == all.last());
            let mut send = apply_effects(node, now, effects);
            apply_effect(node, now, effect, &mut send);
            assert((node@, send@) == spec_effects(before_node, now, all));
            send
        }
    }
}

fn apply_effect(
    node: &mut Node,
    now: Time,
    effect: Effect,
    send: &mut Vec<(Pid, Message)>,
)
    ensures
        (final(node)@, final(send)@)
            == spec_effect(old(node)@, now, effect.deep_view(), old(send)@),
{
    let ghost before_node = node@;
    let ghost before_send = send@;
    let ghost effect_v = effect.deep_view();
    match effect {
        Effect::Store { op, request } => {
            reveal(spec_effect);
            proof {
                lemma_store_request_bounded(request);
                lemma_store_request_realised(request.deep_view());
                lemma_store_request_ext(
                    request,
                    spec_store_request(request.deep_view()),
                );
            }
            send.push((Pid::Store, Message::StoreReq { op, request }));
            assert((node@, send@) == spec_effect(before_node, now, effect_v, before_send));
        }
        Effect::Reply { id, response } => {
            apply_reply(node, now, id, response, send);
            assert((node@, send@) == spec_effect(before_node, now, effect_v, before_send));
        }
        Effect::Wake { after_ms, armed } => {
            reveal(spec_effect);
            node.wake = Some((now.saturating_add(after_ms), armed));
            assert((node@, send@) == spec_effect(before_node, now, effect_v, before_send));
        }
        Effect::Send { address, message } => {
            reveal(spec_effect);
            let output = Output::Dispatch(dispatch(address, message));
            send.push((Pid::Outside, Message::Send(output)));
            assert((node@, send@) == spec_effect(before_node, now, effect_v, before_send));
        }
        Effect::Note(_) => {
            reveal(spec_effect);
            assert((node@, send@) == spec_effect(before_node, now, effect_v, before_send));
        }
    }
}

fn apply_reply(
    node: &mut Node,
    _now: Time,
    id: u64,
    response: Result<Answer, String>,
    send: &mut Vec<(Pid, Message)>,
)
    ensures
        (final(node)@, final(send)@)
            == spec_effect(
                old(node)@,
                _now,
                EffectSpec::Reply {
                    id,
                    response: response.deep_view(),
                },
                old(send)@,
            ),
{
    reveal(spec_effect);
    let pending = remove_pending(&mut node.pending, id);
    if let Some(call) = pending {
        match response {
            Ok(Answer::Step { response, .. }) => {
                let output = Output::Response {
                    client: call.client,
                    id: call.id,
                    response,
                };
                send.push((Pid::Outside, Message::Reply(output)));
            }
            Ok(Answer::Debug { .. }) => {}
            Err(_) => {
                let response = echod_abstract::unavailable(&call.request);
                let output = Output::Response {
                    client: call.client,
                    id: call.id,
                    response,
                };
                send.push((Pid::Outside, Message::Reply(output)));
            }
        }
    }
}

impl Node {
    pub fn new(config: &Config) -> (node: Node)
        ensures
            node@ == spec_initial_node(config.deep_view()),
    {
        let mut core = State::new(copy(config));
        core.set_loops(!config.debug);
        Node {
            core,
            pending: Vec::new(),
            // The production runtime starts the heartbeat loop with one
            // immediate wake before it accepts ordinary traffic.
            wake: Some((0, Armed::Heartbeat)),
            #[cfg(verus_keep_ghost)]
            store_certificates: Ghost(Map::empty()),
        }
    }

    /// One Rover event, executed solely through `State::on_event`.
    pub fn step(
        &self,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<(Node, Vec<(Pid, Message)>)>)
        ensures
            node_results_v(results@) == spec_node_step(self@, now, *event),
    {
        let mut next = copy(self);
        let process_event = match event {
            ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            } => {
                let request = match target(&call.request) {
                    Some(target) => RequestEvent::Protocol(process_call(call, target, now)),
                    None if empty_heartbeat(&call.request) => RequestEvent::EmptyHeartbeat {
                        id: call.id,
                        kind: String::new(),
                        corr: copy(&call.client),
                        action_kind: None,
                    },
                    None => return Vec::new(),
                };
                next.pending.push((call.id, copy(call)));
                Event::Request {
                    clock: now,
                    request,
                }
            }
            ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            } => {
                Event::Store {
                    op: *op,
                    response: copy(response),
                    clock: now,
                }
            },
            ProcessEvent::Timeout => {
                match next.wake {
                    Some((at, armed)) if at <= now => {
                        next.wake = None;
                        Event::Wake { clock: now, armed }
                    }
                    _ => return Vec::new(),
                }
            }
            _ => return Vec::new(),
        };
        let effects = next.core.on_event(process_event);
        #[cfg(verus_keep_ghost)]
        {
            next.store_certificates =
                Ghost(next.core.deep_view().store_certificates);
        }
        let send = apply_effects(&mut next, now, effects);
        let mut results = Vec::new();
        results.push((next, send));
        results
    }
}

impl Process<(), Pid, Message> for Node {
    fn on_event(
        &self,
        _config: &(),
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<(Self, Vec<(Pid, Message)>)> {
        self.step(now, event)
    }
}

pub open spec fn node_results_v(
    results: Seq<(Node, Vec<(Pid, Message)>)>,
) -> Seq<StepResultV<LocalV, Pid, Message>> {
    results.map_values(|result: (Node, Vec<(Pid, Message)>)| {
        StepResultV {
            state: LocalV::Node(result.0@),
            send: result.1@,
        }
    })
}

pub open spec fn store_results_v(
    results: Seq<(Store, Vec<(Pid, Message)>)>,
) -> Seq<StepResultV<LocalV, Pid, Message>> {
    results.map_values(|result: (Store, Vec<(Pid, Message)>)| {
        StepResultV {
            state: LocalV::Store(result.0@),
            send: result.1@,
        }
    })
}

pub open spec fn model_results_v(
    results: Seq<StepResult<Model>>,
) -> Seq<StepResultV<LocalV, Pid, Message>> {
    results.map_values(|result: StepResult<Model>| {
        StepResultV {
            state: result.state@,
            send: result.send@,
        }
    })
}

fn store_step(
    store: &Store,
    event: &ProcessEvent<Pid, Message>,
) -> (results: Vec<(Store, Vec<(Pid, Message)>)>)
    ensures
        store_results_v(results@) == spec_store_step(store@, *event),
{
    let mut results = Vec::new();
    match event {
        ProcessEvent::Receive {
            sender,
            message: Message::StoreReq { op, request },
        } => {
            if seen_has(&store.seen, *sender, *op) {
                results.push((copy(store), Vec::new()));
                proof {
                    assert(store_results_v(results@) =~~= spec_store_step(store@, *event));
                }
                return results;
            }
            let (mut next, response) = store.apply(request);
            next.seen.push((*sender, *op));
            let mut send = Vec::new();
            send.push((*sender, Message::StoreRes { op: *op, response }));
            results.push((next, send));
            proof {
                assert(store_results_v(results@) =~~= spec_store_step(store@, *event));
            }
            results
        }
        _ => {
            proof {
                assert(store_results_v(results@) =~~=
                    Seq::<StepResultV<LocalV, Pid, Message>>::empty());
            }
            results
        }
    }
}

fn same_pid(a: Pid, b: Pid) -> (result: bool)
    ensures
        result == (a == b),
{
    match (a, b) {
        (Pid::Outside, Pid::Outside) => true,
        (Pid::Store, Pid::Store) => true,
        (Pid::Node(x), Pid::Node(y)) => x == y,
        _ => false,
    }
}

fn seen_has(seen: &Vec<(Pid, u64)>, sender: Pid, op: u64) -> (result: bool)
    ensures
        result == seen@.contains((sender, op)),
{
    let mut i = 0;
    while i < seen.len()
        invariant
            i <= seen.len(),
            forall|j: int| 0 <= j < i ==> seen@[j] != (sender, op),
        decreases seen.len() - i,
    {
        let (pid, seen_op) = seen[i];
        if same_pid(pid, sender) && seen_op == op {
            assert(seen@[i as int] == (sender, op));
            return true;
        }
        i += 1;
    }
    false
}

impl RoverModel for Model {
    type Config = Config;
    type Pid = Pid;
    type StateV = LocalV;
    type State = Local;
    type Message = Message;
    type Boundary = BoundaryEvent;

    fn outside(&self) -> Pid {
        Pid::Outside
    }

    fn initial(&self, config: &Config) -> Vec<(Pid, Local)> {
        let mut process = Vec::new();
        process.push((Pid::Node(0), Local::Node(Node::new(config))));
        process.push((
            Pid::Store,
            Local::Store(Store::empty(config.appendable)),
        ));
        process
    }

    fn injectable(&self, _config: &Config, message: &Message) -> bool {
        match message {
            Message::Request(call) =>
                target(&call.request).is_some() || empty_heartbeat(&call.request),
            _ => false,
        }
    }

    fn on_event(
        &self,
        _config: &Config,
        pid: &Pid,
        state: &Local,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<StepResult<Self>> {
        let mut results: Vec<StepResult<Model>> = Vec::new();
        match (pid, state) {
            (Pid::Node(0), Local::Node(node)) => {
                let mut pairs = node.step(now, event);
                let ghost all = pairs@;
                while !pairs.is_empty()
                    invariant
                        results@.len() + pairs@.len() == all.len(),
                        pairs@ == all.skip(results@.len() as int),
                        forall|i: int| 0 <= i < results@.len() ==> {
                            let result = #[trigger] results@[i];
                            StepResultV {
                                state: result.state@,
                                send: result.send@,
                            } == node_results_v(all)[i]
                        },
                    decreases pairs.len(),
                {
                    let ghost k = results@.len() as int;
                    let (next, send) = pairs.remove(0);
                    proof {
                        assert(all.skip(k).remove(0) =~= all.skip(k + 1));
                    }
                    results.push(StepResult {
                        state: Local::Node(next),
                        send,
                    });
                }
                proof {
                    assert(model_results_v(results@) =~= node_results_v(all));
                }
            }
            (Pid::Store, Local::Store(store)) => {
                let mut pairs = store_step(store, event);
                let ghost all = pairs@;
                while !pairs.is_empty()
                    invariant
                        results@.len() + pairs@.len() == all.len(),
                        pairs@ == all.skip(results@.len() as int),
                        forall|i: int| 0 <= i < results@.len() ==> {
                            let result = #[trigger] results@[i];
                            StepResultV {
                                state: result.state@,
                                send: result.send@,
                            } == store_results_v(all)[i]
                        },
                    decreases pairs.len(),
                {
                    let ghost k = results@.len() as int;
                    let (next, send) = pairs.remove(0);
                    proof {
                        assert(all.skip(k).remove(0) =~= all.skip(k + 1));
                    }
                    results.push(StepResult {
                        state: Local::Store(next),
                        send,
                    });
                }
                proof {
                    assert(model_results_v(results@) =~= store_results_v(all));
                }
            }
            _ => {}
        }
        results
    }

    open spec fn spec_outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn spec_initial(&self, config: Config) -> Seq<(Pid, LocalV)> {
        seq![
            (Pid::Node(0), LocalV::Node(spec_initial_node(config.deep_view()))),
            (
                Pid::Store,
                LocalV::Store(echod_concrete::store::StoreV {
                    entries: Seq::empty(),
                    appendable: config.appendable,
                    seen: Seq::empty(),
                }),
            ),
        ]
    }

    open spec fn spec_injectable(&self, _config: Config, message: Message) -> bool {
        match message {
            Message::Request(call) =>
                spec_target(call.request) is Some || spec_empty_heartbeat(call.request),
            _ => false,
        }
    }

    open spec fn spec_on_event(
        &self,
        config: Config,
        pid: Pid,
        state: LocalV,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<RoverStepV<LocalV, Pid, Message>> {
        spec_step(config.deep_view(), pid, state, now, event)
    }

    /// Exactly the admitted request, reply, and send variants are visible.
    /// Store messages, process steps, wakes, and notes project to no boundary
    /// event.
    open spec fn spec_observe(
        &self,
        label: Label<Pid, Message>,
    ) -> Seq<BoundaryEvent> {
        match label {
            Label::Input {
                at,
                message: Message::Request(call),
                ..
            } => seq![BoundaryEvent::Input { at, call }],
            Label::Outside {
                at,
                message: Message::Reply(output),
                ..
            } => seq![BoundaryEvent::Output { at, output }],
            Label::Outside {
                at,
                message: Message::Send(output),
                ..
            } => seq![BoundaryEvent::Output { at, output }],
            _ => Seq::empty(),
        }
    }
}

pub open spec fn spec_initial_node(config: ConfigSpec) -> NodeV {
    NodeV {
        core: StateSpec {
            loops: !config.debug,
            ..crate::state::spec_state_new(config)
        },
        pending: Seq::empty(),
        wake: Some((0, Armed::Heartbeat)),
        #[cfg(verus_keep_ghost)]
        store_certificates: Map::empty(),
    }
}

/// The exact model transition. Its node arm is defined through production
/// `spec_on_event`; the executable arm above calls production `State::on_event`.
pub open spec fn spec_step(
    config: ConfigSpec,
    pid: Pid,
    state: LocalV,
    now: Time,
    event: ProcessEvent<Pid, Message>,
) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match (pid, state) {
        (Pid::Node(0), LocalV::Node(node)) => {
            spec_node_step(node, now, event)
        }
        (Pid::Store, LocalV::Store(store)) => {
            spec_store_step(store, event)
        }
        _ => Seq::empty(),
    }
}

pub open spec fn spec_node_step(
    node: NodeV,
    now: Time,
    event: ProcessEvent<Pid, Message>,
) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match event {
        ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(call),
        } => {
            let request = match spec_target(call.request) {
                Some(target) => Some(RequestEventSpec::Protocol(
                    spec_call(call, target, now),
                )),
                None if spec_empty_heartbeat(call.request) =>
                    Some(RequestEventSpec::EmptyHeartbeat {
                        id: call.id,
                        kind: Seq::empty(),
                        corr: call.client@,
                        action_kind: None,
                    }),
                None => None,
            };
            match request {
            Some(request) => {
                let pending = node.pending.push((call.id, call));
                let event = EventSpec::Request {
                    clock: now,
                    request,
                };
                let (core, effects) = spec_on_event(node.core, event);
                let (next, send) = spec_effects(
                    NodeV {
                        core,
                        pending,
                        store_certificates:
                            core.store_certificates,
                        ..node
                    },
                    now,
                    effects,
                );
                seq![StepResultV { state: LocalV::Node(next), send }]
            }
            None => Seq::empty(),
        }},
        ProcessEvent::Receive {
            sender: Pid::Store,
            message: Message::StoreRes { op, response },
        } => {
            let event = EventSpec::Store { op, response, clock: now };
            let (core, effects) = spec_on_event(node.core, event);
            let (next, send) = spec_effects(
                NodeV {
                    core,
                    store_certificates: core.store_certificates,
                    ..node
                },
                now,
                effects,
            );
            seq![StepResultV { state: LocalV::Node(next), send }]
        }
        ProcessEvent::Timeout => match node.wake {
            Some((at, armed)) if at <= now => {
                let event = EventSpec::Wake { clock: now, armed };
                let (core, effects) = spec_on_event(node.core, event);
                let (next, send) = spec_effects(
                    NodeV {
                        core,
                        wake: None,
                        store_certificates:
                            core.store_certificates,
                        ..node
                    },
                    now,
                    effects,
                );
                seq![StepResultV { state: LocalV::Node(next), send }]
            }
            _ => Seq::empty(),
        },
        _ => Seq::empty(),
    }
}

#[verifier::opaque]
pub open spec fn spec_effects(
    node: NodeV,
    now: Time,
    effects: Seq<EffectSpec>,
) -> (NodeV, Seq<(Pid, Message)>)
    decreases effects.len(),
{
    if effects.len() == 0 {
        (node, Seq::empty())
    } else {
        let effect = effects.last();
        let prefix = effects.drop_last();
        let (node, send) = spec_effects(node, now, prefix);
        spec_effect(node, now, effect, send)
    }
}

#[verifier::opaque]
pub open spec fn spec_effect(
    node: NodeV,
    now: Time,
    effect: EffectSpec,
    send: Seq<(Pid, Message)>,
) -> (NodeV, Seq<(Pid, Message)>) {
    match effect {
        EffectSpec::Store { op, request } => (
            node,
            send.push((Pid::Store, Message::StoreReq {
                op,
                request: spec_store_request(request),
            })),
        ),
        EffectSpec::Wake { after_ms, armed } => (
            NodeV {
                wake: Some((now.saturating_add(after_ms), armed)),
                ..node
            },
            send,
        ),
        EffectSpec::Note(_) => (node, send),
        EffectSpec::Send { address, message } => (
            node,
            send.push((
                Pid::Outside,
                Message::Send(Output::Dispatch(spec_dispatch(address, message))),
            )),
        ),
        EffectSpec::Reply { id, response } => {
            let (found, pending) = spec_take_pending(node.pending, id);
            let node = NodeV { pending, ..node };
            match found {
                None => (node, send),
                Some(call) => {
                    let output = match response {
                        Ok(AnswerSpec::Step { response, .. }) => Some(Output::Response {
                            client: call.client,
                            id: call.id,
                            response,
                        }),
                        Ok(AnswerSpec::Debug { .. }) => None,
                        Err(_) => Some(Output::Response {
                            client: call.client,
                            id: call.id,
                            response: echod_abstract::spec_unavailable(call.request),
                        }),
                    };
                    match output {
                        Some(output) => (
                            node,
                            send.push((Pid::Outside, Message::Reply(output))),
                        ),
                        None => (node, send),
                    }
                }
            }
        }
    }
}

pub open spec fn spec_store_step(
    store: StoreV,
    event: ProcessEvent<Pid, Message>,
) -> Seq<StepResultV<LocalV, Pid, Message>> {
    match event {
        ProcessEvent::Receive {
            sender,
            message: Message::StoreReq { op, request },
        } => {
            if store.seen.contains((sender, op)) {
                seq![StepResultV {
                    state: LocalV::Store(store),
                    send: Seq::empty(),
                }]
            } else {
                let (next, response) = spec_apply(store, request);
                seq![StepResultV {
                    state: LocalV::Store(StoreV {
                        seen: store.seen.push((sender, op)),
                        ..next
                    }),
                    send: seq![(
                        sender,
                        Message::StoreRes { op, response },
                    )],
                }]
            }
        }
        _ => Seq::empty(),
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;
    use echod_rover::rover::RoverModel;
    use echod_types::{
        PromiseCreateReq, PromiseSettleReq, PromiseState, ScheduleGetReq,
        TaskGetReq, TaskHeartbeatReq, Value,
    };

    #[test]
    fn initial_timeout_runs_the_production_heartbeat() {
        let config = Config::memory("node-0");
        let model = Model;
        let initial = model.initial(&config);
        let (pid, local) = &initial[0];

        let outcomes = model.on_event(&config, pid, local, 0, &ProcessEvent::Timeout);

        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].send.len(), 1);
        assert!(matches!(
            &outcomes[0].send[0],
            (Pid::Store, Message::StoreReq { op: 1, .. })
        ));
        assert!(!outcomes[0]
            .send
            .iter()
            .any(|(recipient, _)| *recipient == Pid::Outside));
        let Local::Node(node) = &outcomes[0].state else {
            panic!("the node timeout keeps the node in its local state");
        };
        assert!(node.core.node.members.refresh.is_some());
        assert!(!node.core.timers.started);
        assert!(node.wake.is_none());
    }

    #[test]
    fn production_store_effect_round_trips_through_hidden_store_traffic() {
        let config = Config::memory("node-0");
        let model = Model;
        let initial = model.initial(&config);
        let node_outcome = &model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            0,
            &ProcessEvent::Timeout,
        )[0];
        let (op, request) = node_outcome
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq { op, request } => Some((*op, request.clone())),
                _ => None,
            })
            .expect("heartbeat issues a production store request");

        let store_outcomes = model.on_event(
            &config,
            &initial[1].0,
            &initial[1].1,
            0,
            &ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq { op, request },
            },
        );

        assert_eq!(store_outcomes.len(), 1);
        let response = store_outcomes[0]
            .send
            .iter()
            .find_map(|(recipient, message)| match message {
                Message::StoreRes {
                    op: answer,
                    response,
                } if *recipient == Pid::Node(0) && *answer == op => Some(response.clone()),
                _ => None,
            })
            .expect("the hidden store returns the membership Put");

        let completion = model.on_event(
            &config,
            &initial[0].0,
            &node_outcome.state,
            0,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes { op, response },
            },
        );
        assert_eq!(completion.len(), 1);
        assert_eq!(completion[0].send.len(), 1);
        assert!(matches!(
            &completion[0].send[0],
            (Pid::Store, Message::StoreReq { op: 2, .. })
        ));
        let Local::Node(before) = &node_outcome.state else {
            panic!("the startup timeout produced a node");
        };
        let Local::Node(after) = &completion[0].state else {
            panic!("the membership completion keeps the node");
        };
        assert!(matches!(
            &after.core.node.members.refresh,
            Some(crate::state_node::Refresh::Listing { op: 2, now: 0 })
        ));
        assert_eq!(
            after.core.cache.entries.len(),
            before.core.cache.entries.len()
        );
        assert_eq!(after.core.cache.bytes, before.core.cache.bytes);
        assert_eq!(after.core.timers.started, before.core.timers.started);
        assert_eq!(
            after.core.timers.wheel.armed.len(),
            before.core.timers.wheel.armed.len()
        );
    }

    #[test]
    fn admission_routes_schedules_and_serves_empty_heartbeats() {
        let schedule = Request::ScheduleGet(ScheduleGetReq {
            id: "daily".to_string(),
        });
        assert!(matches!(
            target(&schedule),
            Some(Target::Schedule(id)) if id == "daily"
        ));

        let heartbeat = Request::TaskHeartbeat(TaskHeartbeatReq {
            pid: "worker".to_string(),
            tasks: Vec::new(),
        });
        assert!(target(&heartbeat).is_none());
        assert!(empty_heartbeat(&heartbeat));

        let config = Config::memory("node-0");
        let model = Model;
        let call = BoundaryCall {
            client: "client".to_string(),
            id: 7,
            request: heartbeat,
        };
        assert!(model.injectable(&config, &Message::Request(call.clone())));
        let initial = model.initial(&config);
        let outcomes = model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            1,
            &ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            },
        );
        assert_eq!(outcomes.len(), 1);
        assert!(outcomes[0].send.iter().any(|(recipient, message)| {
            *recipient == Pid::Outside
                && matches!(message, Message::Reply(Output::Response { id: 7, .. }))
        }));
    }

    #[test]
    fn normal_origin_request_enters_production_store_path() {
        let config = Config::memory("node-0");
        let model = Model;
        let call = BoundaryCall {
            client: "client".to_string(),
            id: 8,
            request: Request::TaskGet(TaskGetReq {
                id: "order:task".to_string(),
            }),
        };
        let initial = model.initial(&config);
        let outcomes = model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            1,
            &ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            },
        );

        assert_eq!(outcomes.len(), 1);
        assert!(matches!(
            &outcomes[0].state,
            Local::Node(node) if node.pending.len() == 1
        ));
        assert!(outcomes[0].send.iter().any(|(recipient, message)| {
            *recipient == Pid::Store
                && matches!(message, Message::StoreReq { .. })
        }));
    }

    #[test]
    fn workflow_load_rejects_swapped_document_without_side_effects() {
        let config = Config::memory("node-0");
        let model = Model;
        let initial = model.initial(&config);
        let call = BoundaryCall {
            client: "client".to_string(),
            id: 81,
            request: Request::TaskGet(TaskGetReq {
                id: "requested:task".to_string(),
            }),
        };
        let admitted = &model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            1,
            &ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            },
        )[0];
        let get_op = admitted
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: StoreReq::Get { .. },
                } => Some(*op),
                _ => None,
            })
            .expect("admission emits the workflow Get");

        let wrong = echod_concrete::empty_stored_workflow(
            "different".to_string(),
        );
        let bytes = crate::document::codec::encode(&wrong);
        let etag = echod_concrete::store::etag(&bytes);
        let rejected = &model.on_event(
            &config,
            &Pid::Node(0),
            &admitted.state,
            2,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: get_op,
                    response: StoreRes::Get {
                        result: Ok(Some((bytes, etag))),
                    },
                },
            },
        )[0];

        let Local::Node(before) = &admitted.state else {
            panic!("admission keeps node state");
        };
        let Local::Node(after) = &rejected.state else {
            panic!("rejection keeps node state");
        };
        assert_eq!(after.core.cache.entries.len(), before.core.cache.entries.len());
        assert_eq!(after.core.cache.bytes, before.core.cache.bytes);
        assert!(!rejected.send.iter().any(|(_, message)| {
            matches!(message, Message::StoreReq { .. } | Message::Send(_))
        }));
        assert!(!rejected.send.iter().any(|(_, message)| {
            let Message::Reply(Output::Response {
                id: 81,
                response,
                ..
            }) = message else {
                return false;
            };
            match response {
                echod_types::Response::Promise(r) => r.status < 400,
                echod_types::Response::Schedule(r) => r.status < 400,
                echod_types::Response::Status(r) => r.status < 400,
                echod_types::Response::TaskGet(r) => r.status < 400,
                echod_types::Response::TaskClaim(r) => r.status < 400,
                echod_types::Response::TaskFence(r) => r.status < 400,
            }
        }));
    }

    #[test]
    fn schedule_load_rejects_swapped_document_without_side_effects() {
        let config = Config::memory("node-0");
        let model = Model;
        let initial = model.initial(&config);
        let call = BoundaryCall {
            client: "client".to_string(),
            id: 82,
            request: Request::ScheduleGet(ScheduleGetReq {
                id: "requested".to_string(),
            }),
        };
        let admitted = &model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            1,
            &ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            },
        )[0];
        let get_op = admitted
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: StoreReq::Get { .. },
                } => Some(*op),
                _ => None,
            })
            .expect("admission emits the schedule Get");

        let wrong = echod_concrete::empty_stored_schedule(
            "different".to_string(),
        );
        let bytes = crate::document::codec::encode(&wrong);
        let etag = echod_concrete::store::etag(&bytes);
        let rejected = &model.on_event(
            &config,
            &Pid::Node(0),
            &admitted.state,
            2,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: get_op,
                    response: StoreRes::Get {
                        result: Ok(Some((bytes, etag))),
                    },
                },
            },
        )[0];

        let Local::Node(before) = &admitted.state else {
            panic!("admission keeps node state");
        };
        let Local::Node(after) = &rejected.state else {
            panic!("rejection keeps node state");
        };
        assert_eq!(after.core.cache.entries.len(), before.core.cache.entries.len());
        assert_eq!(after.core.cache.bytes, before.core.cache.bytes);
        assert!(!rejected.send.iter().any(|(_, message)| {
            matches!(message, Message::StoreReq { .. } | Message::Send(_))
        }));
        assert!(!rejected.send.iter().any(|(_, message)| {
            let Message::Reply(Output::Response {
                id: 82,
                response,
                ..
            }) = message else {
                return false;
            };
            match response {
                echod_types::Response::Promise(r) => r.status < 400,
                echod_types::Response::Schedule(r) => r.status < 400,
                echod_types::Response::Status(r) => r.status < 400,
                echod_types::Response::TaskGet(r) => r.status < 400,
                echod_types::Response::TaskClaim(r) => r.status < 400,
                echod_types::Response::TaskFence(r) => r.status < 400,
            }
        }));
    }

    #[test]
    fn workflow_refresh_mismatch_does_not_poison_cache() {
        let config = Config::memory("node-0");
        let model = Model;
        let mut initial = model.initial(&config);
        let cached_document = echod_concrete::empty_stored_workflow(
            "requested".to_string(),
        );
        let cached_bytes = crate::document::codec::encode(&cached_document);
        let cached_etag = echod_concrete::store::etag(&cached_bytes);
        let cached_weight = cached_bytes.len() as u64;
        let Local::Node(node) = &mut initial[0].1 else {
            panic!("slot zero is the node");
        };
        node.core.cache.entries.push(crate::cache::Entry {
            origin: "requested".to_string(),
            cached: crate::cache::Cached {
                loaded: crate::document::Loaded {
                    document: cached_document,
                    change_count: 0,
                    bytes: cached_weight,
                    append_certified: false,
                },
                etag: cached_etag,
                filled_at: 0,
            },
        });
        node.core.cache.bytes = cached_weight;

        let call = BoundaryCall {
            client: "client".to_string(),
            id: 83,
            request: Request::TaskGet(TaskGetReq {
                id: "requested:task".to_string(),
            }),
        };
        let admitted = &model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            1,
            &ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            },
        )[0];
        let get_op = admitted
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: StoreReq::GetIfNoneMatch { .. },
                } => Some(*op),
                _ => None,
            })
            .expect("cached admission emits a conditional Get");

        let wrong = echod_concrete::empty_stored_workflow(
            "different".to_string(),
        );
        let bytes = crate::document::codec::encode(&wrong);
        let etag = echod_concrete::store::etag(&bytes);
        let rejected = &model.on_event(
            &config,
            &Pid::Node(0),
            &admitted.state,
            2,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: get_op,
                    response: StoreRes::GetIfNoneMatch {
                        result: Ok(echod_concrete::store::Read::Body(
                            bytes,
                            etag,
                        )),
                    },
                },
            },
        )[0];

        let Local::Node(after) = &rejected.state else {
            panic!("rejection keeps node state");
        };
        assert_eq!(after.core.cache.entries.len(), 1);
        assert_eq!(after.core.cache.entries[0].origin, "requested");
        assert!(matches!(
            &after.core.cache.entries[0].cached.loaded.document,
            echod_concrete::StoredDocument::Workflow(workflow)
                if workflow.document == "requested"
        ));
        assert!(!rejected.send.iter().any(|(_, message)| {
            matches!(message, Message::StoreReq { .. } | Message::Send(_))
        }));
    }

    #[test]
    fn successful_loaded_request_closes_direct_write_branch() {
        let config = Config::memory("node-0");
        let model = Model;
        let initial = model.initial(&config);
        let value = |data: &str| Value {
            headers: Vec::new(),
            data: Some(data.to_string()),
        };
        let create = Request::PromiseCreate(PromiseCreateReq {
            id: "order:promise".to_string(),
            timeout_at: 10_000,
            param: value("input"),
            tags: Vec::new(),
        });
        let empty =
            echod_concrete::empty_stored_workflow("order".to_string());
        let (body, _, _, _) = echod_concrete::request_transition(
            echod_concrete::stored_body(&empty),
            &create,
            1,
            config.retry_timeout,
        );
        let stored = echod_concrete::advance_stored(&empty, body, 1);
        let bytes = crate::document::codec::encode(&stored);

        let call = BoundaryCall {
            client: "client".to_string(),
            id: 9,
            request: Request::PromiseSettle(PromiseSettleReq {
                id: "order:promise".to_string(),
                state: PromiseState::Resolved,
                value: value("done"),
            }),
        };
        let admitted = &model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            2,
            &ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            },
        )[0];
        let (get_op, get) = admitted
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: request @ StoreReq::Get { .. },
                } => Some((*op, request.clone())),
                _ => None,
            })
            .expect("admission emits the workflow Get");
        let key = match &get {
            StoreReq::Get { key } => key.clone(),
            _ => unreachable!(),
        };
        let store = Local::Store(Store {
            entries: vec![echod_concrete::store::Entry {
                key,
                body: bytes,
                version: 1,
            }],
            appendable: false,
            seen: Vec::new(),
        });
        let get_answer = &model.on_event(
            &config,
            &Pid::Store,
            &store,
            3,
            &ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: get_op,
                    request: get,
                },
            },
        )[0];
        let response = get_answer
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreRes { op, response } if *op == get_op =>
                    Some(response.clone()),
                _ => None,
            })
            .expect("the Store returns the matching Get response");
        assert!(matches!(
            response,
            StoreRes::Get { result: Ok(Some(_)) }
        ));

        let continued = &model.on_event(
            &config,
            &Pid::Node(0),
            &admitted.state,
            4,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: get_op,
                    response,
                },
            },
        )[0];
        assert!(continued.send.iter().any(|(recipient, message)| {
            *recipient == Pid::Store
                && matches!(
                    message,
                    Message::StoreReq {
                        request: StoreReq::PutIfMatch { .. },
                        ..
                    }
                )
        }));
        let (write_op, write) = continued
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: request @ StoreReq::PutIfMatch { .. },
                } => Some((*op, request.clone())),
                _ => None,
            })
            .expect("successful load emits the conditional write");
        let write_answer = &model.on_event(
            &config,
            &Pid::Store,
            &get_answer.state,
            5,
            &ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: write_op,
                    request: write,
                },
            },
        )[0];
        let write_response = write_answer
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreRes { op, response } if *op == write_op =>
                    Some(response.clone()),
                _ => None,
            })
            .expect("the Store returns the matching write response");
        assert!(matches!(
            write_response,
            StoreRes::PutIfMatch { result: Ok(_) }
        ));

        let after_write = &model.on_event(
            &config,
            &Pid::Node(0),
            &continued.state,
            6,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: write_op,
                    response: write_response,
                },
            },
        )[0];
        assert!(after_write.send.iter().any(|(recipient, message)| {
            *recipient == Pid::Outside
                && matches!(
                    message,
                    Message::Reply(Output::Response { id: 9, .. })
                )
        }));
    }

    #[test]
    fn successful_loaded_request_closes_previous_deadline_delete_branch() {
        use crate::verified::node::{Armed as RememberedArmed, Key};

        let config = Config::memory("node-0");
        let model = Model;
        let value = |data: &str| Value {
            headers: Vec::new(),
            data: Some(data.to_string()),
        };
        let create = Request::PromiseCreate(PromiseCreateReq {
            id: "order:promise".to_string(),
            timeout_at: 10_000,
            param: value("input"),
            tags: Vec::new(),
        });
        let empty =
            echod_concrete::empty_stored_workflow("order".to_string());
        let (body, _, _, _) = echod_concrete::request_transition(
            echod_concrete::stored_body(&empty),
            &create,
            1,
            config.retry_timeout,
        );
        let stored = echod_concrete::advance_stored(&empty, body, 1);
        let bytes = crate::document::codec::encode(&stored);
        let loaded_etag = echod_concrete::store::etag(&bytes).0;
        let mut initial = model.initial(&config);
        match &mut initial[0].1 {
            Local::Node(node) => node.core.node.core.set_armed(
                "order",
                Some(RememberedArmed {
                    key: Key {
                        origin: "order".to_string(),
                        at: 10_000,
                        token: 77,
                    },
                    etag: loaded_etag,
                }),
            ),
            Local::Store(_) => panic!("slot zero is the node"),
        }

        let call = BoundaryCall {
            client: "client".to_string(),
            id: 10,
            request: Request::PromiseSettle(PromiseSettleReq {
                id: "order:promise".to_string(),
                state: PromiseState::Resolved,
                value: value("done"),
            }),
        };
        let admitted = &model.on_event(
            &config,
            &initial[0].0,
            &initial[0].1,
            2,
            &ProcessEvent::Receive {
                sender: Pid::Outside,
                message: Message::Request(call),
            },
        )[0];
        let (get_op, get) = admitted
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: request @ StoreReq::Get { .. },
                } => Some((*op, request.clone())),
                _ => None,
            })
            .expect("admission emits the workflow Get");
        let key = match &get {
            StoreReq::Get { key } => key.clone(),
            _ => unreachable!(),
        };
        let store = Local::Store(Store {
            entries: vec![echod_concrete::store::Entry {
                key,
                body: bytes,
                version: 1,
            }],
            appendable: false,
            seen: Vec::new(),
        });
        let get_answer = &model.on_event(
            &config,
            &Pid::Store,
            &store,
            3,
            &ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: get_op,
                    request: get,
                },
            },
        )[0];
        let get_response = get_answer
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreRes { op, response } if *op == get_op =>
                    Some(response.clone()),
                _ => None,
            })
            .expect("the Store returns the matching Get response");
        let continued = &model.on_event(
            &config,
            &Pid::Node(0),
            &admitted.state,
            4,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: get_op,
                    response: get_response,
                },
            },
        )[0];
        let (write_op, write) = continued
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: request @ StoreReq::PutIfMatch { .. },
                } => Some((*op, request.clone())),
                _ => None,
            })
            .expect("successful load emits the conditional write");
        let write_answer = &model.on_event(
            &config,
            &Pid::Store,
            &get_answer.state,
            5,
            &ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: write_op,
                    request: write,
                },
            },
        )[0];
        let write_response = write_answer
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreRes { op, response } if *op == write_op =>
                    Some(response.clone()),
                _ => None,
            })
            .expect("the Store returns the matching write response");
        let after_write = &model.on_event(
            &config,
            &Pid::Node(0),
            &continued.state,
            6,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: write_op,
                    response: write_response,
                },
            },
        )[0];
        let (delete_op, delete) = after_write
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreReq {
                    op,
                    request: request @ StoreReq::Del { .. },
                } => Some((*op, request.clone())),
                _ => None,
            })
            .expect("the previous deadline key is deleted");
        assert!(!after_write.send.iter().any(|(_, message)| {
            matches!(message, Message::Reply(_))
        }));
        let delete_answer = &model.on_event(
            &config,
            &Pid::Store,
            &write_answer.state,
            7,
            &ProcessEvent::Receive {
                sender: Pid::Node(0),
                message: Message::StoreReq {
                    op: delete_op,
                    request: delete,
                },
            },
        )[0];
        let delete_response = delete_answer
            .send
            .iter()
            .find_map(|(_, message)| match message {
                Message::StoreRes { op, response } if *op == delete_op =>
                    Some(response.clone()),
                _ => None,
            })
            .expect("the Store returns the matching delete response");
        assert!(matches!(
            delete_response,
            StoreRes::Del { result: Ok(()) }
        ));
        let completed = &model.on_event(
            &config,
            &Pid::Node(0),
            &after_write.state,
            8,
            &ProcessEvent::Receive {
                sender: Pid::Store,
                message: Message::StoreRes {
                    op: delete_op,
                    response: delete_response,
                },
            },
        )[0];
        assert!(completed.send.iter().any(|(recipient, message)| {
            *recipient == Pid::Outside
                && matches!(
                    message,
                    Message::Reply(Output::Response { id: 10, .. })
                )
        }));
    }
}
