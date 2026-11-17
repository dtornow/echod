//! The core driven by hand: a store that is a map, a clock that is a
//! number, no runtime. Every effect the core asks for is performed here,
//! in order, and the answers fed back; what comes out is what a node does.

use std::collections::BTreeMap;

use echod_logic::types::{Armed, Effect, Etag, Event, Note, Read, RequestEvent, StoreReq, StoreRes, SweepOutcome};
use echod_logic::Message;
use echod_logic::{Call, Config, DebugCall, State};
use echod::admit::{self, Admission, DebugOp};
use echod::codec;
use resonate_core::types::{RequestEnvelope, RequestHead, PROTOCOL_VERSION};
use serde_json::{json, Value};

/// The bucket as a map: every call answered at once, in order.
#[derive(Default)]
struct Bucket {
    objects: BTreeMap<String, (Vec<u8>, u64)>,
}

impl Bucket {
    fn etag(b: &[u8], v: u64) -> Etag {
        Etag(format!("{}-{v}", b.len()))
    }

    fn call(&mut self, request: StoreReq) -> StoreRes {
        match request {
            StoreReq::Get { key } => StoreRes::Get { result: Ok(self.objects.get(&key).map(|(b, v)| (b.clone(), Self::etag(b, *v)))) },
            StoreReq::GetIfNoneMatch { key, etag } => StoreRes::GetIfNoneMatch { result: Ok(match self.objects.get(&key) {
                None => Read::Absent,
                Some((b, v)) if Self::etag(b, *v) == etag => Read::NotModified,
                Some((b, v)) => Read::Body(b.clone(), Self::etag(b, *v)),
            }) },
            StoreReq::PutIfMatch { key, body, etag } => match self.objects.get(&key) {
                Some((b, v)) if Self::etag(b, *v) == etag => {
                    let nv = v + 1;
                    let e = Self::etag(&body, nv);
                    self.objects.insert(key, (body, nv));
                    StoreRes::PutIfMatch { result: Ok(e) }
                }
                _ => StoreRes::PutIfMatch { result: Err(echod_logic::types::StoreError::PreconditionFailed) },
            },
            StoreReq::PutIfNoneMatch { key, body } => {
                if self.objects.contains_key(&key) {
                    return StoreRes::PutIfNoneMatch { result: Err(echod_logic::types::StoreError::PreconditionFailed) };
                }
                let e = Self::etag(&body, 1);
                self.objects.insert(key, (body, 1));
                StoreRes::PutIfNoneMatch { result: Ok(e) }
            }
            StoreReq::AppIfMatch { .. } => StoreRes::AppIfMatch { result: Err(echod_logic::types::StoreError::Unavailable("no appends".into())) },
            StoreReq::Put { key, body } => {
                let v = self.objects.get(&key).map(|(_, v)| v + 1).unwrap_or(1);
                self.objects.insert(key, (body, v));
                StoreRes::Put { result: Ok(()) }
            }
            StoreReq::Del { key } => {
                self.objects.remove(&key);
                StoreRes::Del { result: Ok(()) }
            }
            StoreReq::List { prefix, max_keys } => StoreRes::List { result: Ok(self.objects.keys().filter(|k| k.starts_with(&prefix)).take(max_keys).cloned().collect()) },
            StoreReq::ListPrefixes { prefix } => {
                let mut out: Vec<String> = Vec::new();
                for k in self.objects.keys().filter(|k| k.starts_with(&prefix)) {
                    if let Some(i) = k[prefix.len()..].find('/') {
                        let p = k[..prefix.len() + i + 1].to_string();
                        if out.last() != Some(&p) {
                            out.push(p);
                        }
                    }
                }
                StoreRes::ListPrefixes { result: Ok(out) }
            }
        }
    }
}

/// A node and its world: the state, the bucket, the clock, and what came
/// out that was not a store call.
struct ReplayProbe {
    config: Config,
    loops: bool,
    history: Vec<Event>,
    branch: echod_logic::replay::ReplayBranch,
    effects: Vec<Vec<echod_logic::production_rover::ProductionEffectData>>,
    direct_time: std::time::Duration,
    replay_time: std::time::Duration,
}

impl Drop for ReplayProbe {
    fn drop(&mut self) {
        eprintln!("replay probe: {} inputs, direct {:?}, replay {:?}", self.history.len(), self.direct_time, self.replay_time);
    }
}

struct Harness {
    replay_probe: Option<ReplayProbe>,
    state: State,
    bucket: Bucket,
    clock: u64,
    replies: Vec<(u64, Result<echod_logic::Answer, String>)>,
    sent: Vec<String>,
    notes: Vec<Note>,
    wake_after: Option<u64>,
    wake_armed: Armed,
    next_request: u64,
}

impl Harness {
    fn new(id: &str) -> Self {
        let mut cfg = Config::memory(id);
        cfg.timer_bucket_ms = 1_000;
        cfg.heartbeat_ms = 100;
        cfg.node_ttl_ms = 1_000;
        Self { replay_probe: None, state: State::new(cfg), bucket: Bucket::default(), clock: 1_000_000, replies: Vec::new(), sent: Vec::new(), notes: Vec::new(), wake_after: None, wake_armed: Armed::Wheel, next_request: 1 }
    }

    fn replay_checked(id: &str) -> Self {
        let mut h = Self::new(id);
        h.replay_probe = Some(ReplayProbe {
            config: h.state.config().clone(), loops: false, history: Vec::new(),
            branch: echod_logic::replay::ReplayBranch::new(h.state.config().clone(), false),
            effects: Vec::new(),
            direct_time: std::time::Duration::ZERO, replay_time: std::time::Duration::ZERO,
        });
        h
    }

    fn step(&mut self, event: Event) -> Vec<Effect> {
        let recorded = self.replay_probe.as_ref().map(|_| echod_logic::replay::copy_event(&event));
        let start = std::time::Instant::now();
        let effects = self.state.on_event(event);
        let elapsed = start.elapsed();
        if let Some(probe) = &mut self.replay_probe {
            probe.direct_time += elapsed;
            let recorded = recorded.unwrap();
            let start = std::time::Instant::now();
            let saved = probe.branch.clone();
            let (next, replayed) = probe.branch.step(&recorded);
            assert_eq!(probe.branch, saved);
            assert_ne!(next, saved);
            probe.branch = next;
            probe.replay_time += start.elapsed();
            assert!(effects == replayed, "replay differed at input {}", probe.history.len());
            probe.effects.push(replayed.into_iter().map(echod_logic::production_rover::effect_out).collect());
            probe.history.push(recorded);
        }
        effects
    }

    /// One event in, and every store call it leads to answered, until the
    /// core asks for nothing more of the store.
    fn apply(&mut self, event: Event) {
        let pending = self.step(event);
        self.perform_all(pending);
    }

    fn perform_all(&mut self, mut pending: Vec<Effect>) {
        while !pending.is_empty() {
            let mut next = Vec::new();
            for e in pending {
                match e {
                    Effect::Store { op, request } => {
                        let response = self.bucket.call(request);
                        next.extend(self.step(Event::Store { op, response, clock: self.clock }));
                    }
                    Effect::Reply { id, response } => self.replies.push((id, response)),
                    Effect::Send { address, message } => {
                        let body = match &message {
                            Message::Execute { task_id, .. } => format!("execute {task_id}"),
                            Message::Unblock(r) => format!("unblock {}", r.id),
                        };
                        self.sent.push(format!("{address} {body}"));
                    }
                    Effect::Wake { after_ms, armed } => {
                        self.wake_after = Some(after_ms);
                        self.wake_armed = armed;
                    }
                    Effect::Note(n) => self.notes.push(n),
                }
            }
            pending = next;
        }
    }

    fn start(&mut self, loops: bool) {
        if let Some(probe) = &mut self.replay_probe {
            assert!(probe.history.is_empty(), "initial loop policy precedes recorded events");
            probe.loops = loops;
            probe.branch = echod_logic::replay::ReplayBranch::new(probe.config.clone(), loops);
        }
        self.state.set_loops(loops);
        self.apply(Event::Wake { clock: self.clock, armed: Armed::Heartbeat });
    }

    fn request(&mut self, kind: &str, data: Value) -> (u16, Value) {
        let id = self.next_request;
        self.next_request += 1;
        let envelope = RequestEnvelope { kind: kind.to_string(), head: RequestHead { corr_id: format!("c{id}"), version: PROTOCOL_VERSION.to_string(), auth: None, debug_time: None }, data };
        match admit::admit(&envelope, self.clock, self.state.config().debug) {
            Admission::Rejected(resp) => (resp.head.status as u16, resp.data),
            Admission::Request(d) => {
                self.apply(Event::Request {
                    clock: self.clock,
                    request: RequestEvent::Protocol(Call { id, kind: d.kind, corr: d.corr, target: d.target, request: d.request, action_kind: d.action_kind, now: d.now, pinned: d.pinned, then: d.then }),
                });
                self.take(id)
            }
            Admission::Debug { kind, corr, op } => {
                let call = match op {
                    DebugOp::Reset => DebugCall::Reset { id, kind, corr },
                    DebugOp::Snap => DebugCall::Snap { id, kind, corr },
                    DebugOp::Tick { time } => DebugCall::Tick { id, kind, corr, time },
                };
                self.apply(Event::Request {
                    clock: self.clock,
                    request: RequestEvent::Debug(call),
                });
                self.take(id)
            }
        }
    }

    fn take(&mut self, id: u64) -> (u16, Value) {
        let (rid, r) = self.replies.pop().expect("an answer");
        assert_eq!(rid, id);
        let answer = r.expect("served");
        let r = codec::envelope(&answer);
        (r.head.status as u16, r.data)
    }

    /// Time passes: the clock moves and the core gets a tick whenever it
    /// asked for one, as the executor's timer would give it.
    fn advance(&mut self, ms: u64) {
        let until = self.clock + ms;
        while self.clock < until {
            let step = self.wake_after.unwrap_or(until - self.clock).min(until - self.clock).max(1);
            self.clock += step;
            self.wake_after = None;
            self.apply(Event::Wake { clock: self.clock, armed: self.wake_armed.clone() });
        }
    }

    fn keys(&self, prefix: &str) -> Vec<String> {
        self.bucket.objects.keys().filter(|k| k.starts_with(prefix)).cloned().collect()
    }

    fn submit_held(&mut self, kind: &str, data: Value) -> (u64, Vec<(u64, StoreReq)>) {
        let id = self.next_request;
        self.next_request += 1;
        let envelope = RequestEnvelope {
            kind: kind.to_string(),
            head: RequestHead { corr_id: format!("c{id}"), version: PROTOCOL_VERSION.to_string(), auth: None, debug_time: None },
            data,
        };
        let Admission::Request(d) = admit::admit(&envelope, self.clock, self.state.config().debug) else {
            panic!("expected an admitted protocol request");
        };
        let effects = self.step(Event::Request {
            clock: self.clock,
            request: RequestEvent::Protocol(Call { id, kind: d.kind, corr: d.corr, target: d.target, request: d.request, action_kind: d.action_kind, now: d.now, pinned: d.pinned, then: d.then }),
        });
        (id, self.hold_store(effects))
    }

    fn hold_store(&mut self, effects: Vec<Effect>) -> Vec<(u64, StoreReq)> {
        let mut calls = Vec::new();
        for effect in effects {
            match effect {
                Effect::Store { op, request } => calls.push((op, request)),
                other => self.perform_all(vec![other]),
            }
        }
        calls
    }

    fn answer_held(&mut self, op: u64, response: StoreRes) -> Vec<(u64, StoreReq)> {
        let effects = self.step(Event::Store { op, response, clock: self.clock });
        self.hold_store(effects)
    }
}

#[test]
fn startup_store_failure_is_preserved_by_replay() {
    let mut h = Harness::replay_checked("n1");
    let (id, calls) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    assert!(!calls.is_empty(), "startup still performs membership I/O");
    assert!(!h.state.acting());
    assert!(h.replies.is_empty(), "the request is still waiting on its read");
    let (op, _) = calls.into_iter().find(|(_, request)| matches!(request, StoreReq::Get { .. }))
        .expect("the document read");
    h.answer_held(op, StoreRes::Get {
        result: Err(echod_logic::types::StoreError::Unavailable("startup read failed".into())),
    });
    let (reply_id, reply) = h.replies.pop().expect("an explicit unavailable reply");
    assert_eq!(reply_id, id);
    assert!(reply.is_err(), "the unavailable response must not disappear");
    certify_recorded_production(&h);
}

#[test]
fn replay_overhead_on_a_short_request_trace() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    for i in 0..48 {
        assert_eq!(h.request("promise.get", json!({ "id": format!("p{i}:1") })).0, 404);
    }
    let count = h.replay_probe.as_ref().unwrap().history.len();
    assert!((96..=128).contains(&count));
}

#[test]
fn different_documents_have_concurrent_flights_and_correlated_replies() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    let (a, mut first) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    let (b, mut second) = h.submit_held("promise.get", json!({ "id": "b:1" }));
    assert_eq!(first.len(), 1);
    assert_eq!(second.len(), 1);
    assert!(h.replies.is_empty());
    let (op_b, request_b) = second.pop().unwrap();
    let response_b = h.bucket.call(request_b);
    assert!(h.answer_held(op_b, response_b.clone()).is_empty());
    assert_eq!(h.take(b).0, 404);
    assert!(h.answer_held(op_b, response_b).is_empty());
    assert!(h.replies.is_empty(), "a duplicate response must not complete another flight");
    let (op_a, request_a) = first.pop().unwrap();
    let response_a = h.bucket.call(request_a);
    assert!(h.answer_held(op_a, response_a).is_empty());
    assert_eq!(h.take(a).0, 404);
}

fn certify_recorded_production(h: &Harness) {
    use echod_logic::production_rover::{config_out, event_out, NodeSpec, Pid, ProductionModelConfig, ProductionWireMessage};
    use rover_spec::rover::comm::{BoundaryEvent, ProcessEvent};
    use rover_exec::{Action, Driver};
    let probe = h.replay_probe.as_ref().unwrap();
    let config = ProductionModelConfig { node: config_out(&probe.config), loops: probe.loops };
    let mut actions = std::collections::VecDeque::new();
    let mut at = 0;
    for (event, effects) in probe.history.iter().zip(&probe.effects) {
        let clock = match event {
            Event::Request { clock, .. } | Event::Store { clock, .. } | Event::Wake { clock, .. } => *clock,
        };
        assert!(clock >= at);
        if clock > at { actions.push_back(Action::Clock { at: clock }); at = clock; }
        let message = ProductionWireMessage::Input(event_out(echod_logic::replay::copy_event(event)));
        actions.push_back(Action::Inject { recipient: Pid::Node(0), at, message: message.clone() });
        actions.push_back(Action::Process {
            slot: 0, process: Pid::Node(0), at,
            event: ProcessEvent::Receive { sender: Pid::Outside, message }, outcome: 0,
        });
        for effect in effects {
            actions.push_back(Action::Observe { sender: Pid::Node(0), at, message: ProductionWireMessage::Effect(effect.clone()) });
        }
    }
    let maximum = actions.len();
    let result = rover_exec::exec(&NodeSpec, &config, maximum, move |_: Driver<'_, NodeSpec>| actions.pop_front())
        .expect("production Rover execution and independent certificate replay");
    let observed: Vec<_> = result.trace.into_iter().filter_map(|event| match event {
        BoundaryEvent::Output { message: ProductionWireMessage::Effect(effect), .. } => Some(effect),
        _ => None,
    }).collect();
    assert_eq!(observed, probe.effects.iter().flatten().cloned().collect::<Vec<_>>());
}

fn fleet_request(id: u64, kind: &str, data: Value, now: u64) -> echod_logic::production_rover::ProductionWireMessage {
    let envelope = RequestEnvelope {
        kind: kind.into(),
        head: RequestHead { corr_id: format!("c{id}"), version: PROTOCOL_VERSION.into(), auth: None, debug_time: None },
        data,
    };
    let Admission::Request(d) = admit::admit(&envelope, now, false) else { panic!("admitted request"); };
    echod_logic::production_rover::ProductionWireMessage::Input(echod_logic::production_rover::event_out(Event::Request {
        clock: now,
        request: RequestEvent::Protocol(Call { id, kind: d.kind, corr: d.corr, target: d.target, request: d.request,
            action_kind: d.action_kind, now: d.now, pinned: d.pinned, then: d.then }),
    }))
}

fn drive_fleet<M: rover_exec::Spec<Proc = echod_logic::production_rover::FleetBridge>>(
    model: &M,
    config: &echod_logic::production_rover::ProductionFleetConfig,
    inputs: Vec<(u64, echod_logic::production_rover::Pid, echod_logic::production_rover::ProductionWireMessage)>,
    clocks: Vec<u64>,
    fault: Option<(String, usize)>,
    hold: Option<(echod_logic::production_rover::Pid, String, String)>,
) -> rover_exec::ExecResult<echod_logic::production_rover::Pid, echod_logic::production_rover::ProductionWireMessage>
where M::Spec: rover_spec::rover::RoverSpec::Spec<
    Config = echod_logic::production_rover::ProductionFleetConfig,
    Pid = echod_logic::production_rover::Pid,
    Message = echod_logic::production_rover::ProductionWireMessage,
> {
    use echod_logic::production_rover::{Pid, ProductionWireMessage};
    use rover_exec::{Action, Driver};
    use rover_spec::rover::comm::ProcessEvent;
    let mut inputs: std::collections::VecDeque<_> = inputs.into();
    let mut clocks: std::collections::VecDeque<_> = clocks.into();
    let mut received = std::collections::BTreeSet::new();
    let mut observed = std::collections::BTreeSet::new();
    let mut failed = false;
    let mut released = false;
    rover_exec::exec(model, config, 2_000, move |driver: Driver<'_, M>| {
        if inputs.front().is_some_and(|(at, _, _)| *at <= driver.now) {
            let (_, recipient, message) = inputs.pop_front().unwrap();
            return Some(Action::Inject { recipient, at: driver.now, message });
        }
        for action in driver.observe {
            if let Action::Observe { sender, message, .. } = action {
                if let (Some((_, _, client)), ProductionWireMessage::PublicResult { call, .. }) = (&hold, message) {
                    released |= call.client == *client;
                }
                if observed.insert((*sender, message.clone())) { return Some(action.clone()); }
            }
        }
        for action in driver.internal {
            if let Action::Process { process, event: ProcessEvent::Receive { sender, message }, outcome, .. } = action {
                let key = (*process, *sender, message.clone());
                if received.contains(&key) { continue; }
                if !released && matches!((&hold, message),
                    (Some((node, target, _)), ProductionWireMessage::StoreCall { request: StoreReq::PutIfMatch { key, .. }, .. })
                        if *node == *sender && key == target) { continue; }
                let fault_here = !failed && *process == Pid::Store && matches!((message, &fault),
                    (ProductionWireMessage::StoreCall { request: StoreReq::PutIfMatch { key, .. } | StoreReq::PutIfNoneMatch { key, .. }, .. },
                     Some((fail_key, _))) if key == fail_key);
                let chosen = if fault_here { fault.as_ref().unwrap().1 } else { 0 };
                if *outcome != chosen { continue; }
                received.insert(key);
                failed |= fault_here;
                return Some(action.clone());
            }
        }
        if let Some(action) = driver.internal.iter().find(|action| matches!(action,
            Action::Process { event: ProcessEvent::Timeout, .. })) {
            return Some(action.clone());
        }
        while clocks.front().is_some_and(|at| *at <= driver.now) { clocks.pop_front(); }
        let next = clocks.front().copied().into_iter().chain(inputs.front().map(|(at, _, _)| *at)).min();
        next.map(|at| Action::Clock { at })
    }).expect("causal fleet execution and independent replay")
}

#[test]
fn production_fleet_routes_concurrent_local_operations_and_ambiguous_store_failures() {
    use echod_logic::production_rover::{config_out, Pid, ProductionFleetConfig, ProductionWireMessage, ProductionEffectData, ProductionAnswerData};
    use rover_spec::rover::comm::{BoundaryEvent, ProcessEvent};
    use rover_exec::Action;
    for failure in [None, Some(1), Some(2)] {
        let config = ProductionFleetConfig {
            nodes: vec![config_out(&Config::memory("n1")), config_out(&Config::memory("n2"))],
            loops: false, appendable: false, fault: Some("causal store failure".into()),
        };
        let inputs = vec![
            (0, Pid::Node(0), fleet_request(1, "task.fence", json!({
                "id": "a:missing", "version": 0,
                "action": { "kind": "promise.create", "head": {}, "data": { "id": "b:child", "timeoutAt": 10_000, "tags": {} } }
            }), 0)),
            (0, Pid::Node(0), fleet_request(2, "promise.get", json!({ "id": "b:child" }), 0)),
            (0, Pid::Node(1), fleet_request(1, "promise.create", json!({ "id": "c:other", "timeoutAt": 10_000, "tags": {} }), 0)),
        ];
        let execution = drive_fleet(&echod_logic::production_rover::FleetSpec, &config, inputs, vec![], failure.map(|outcome| ("wf/b".into(), outcome)), None);
        let replies: Vec<_> = execution.trace.iter().filter_map(|event| match event {
            BoundaryEvent::Output { sender, message: ProductionWireMessage::Effect(ProductionEffectData::Reply { id, response }), .. } =>
                Some((*sender, *id, response)),
            _ => None,
        }).collect();
        assert_eq!(replies.len(), 3);
        let detached = replies.iter().find(|(node, id, _)| *node == Pid::Node(0) && *id == 1).unwrap().2;
        if failure.is_some() {
            assert!(detached.is_err());
        } else {
            assert!(matches!(detached, Ok(ProductionAnswerData::Step { kind, corr, response: echod_logic::verified::Response::TaskFence(r), .. })
                if kind == "task.fence" && corr == "c1" && r.status == 404));
        }
        let get = replies.iter().find(|(node, id, _)| *node == Pid::Node(0) && *id == 2).unwrap().2;
        assert!(matches!(get, Ok(ProductionAnswerData::Step { response: echod_logic::verified::Response::Promise(r), .. })
            if r.status == if failure == Some(1) { 404 } else { 200 }));
        let independent = replies.iter().find(|(node, id, _)| *node == Pid::Node(1) && *id == 1).unwrap().2;
        assert!(matches!(independent, Ok(ProductionAnswerData::Step { response: echod_logic::verified::Response::Promise(r), .. })
            if r.status == 200 && r.promise.as_ref().is_some_and(|p| p.id == "c:other")));
        let mut operations = [std::collections::BTreeSet::new(), std::collections::BTreeSet::new()];
        for action in &execution.certificate {
            if let Action::Process { process: Pid::Store, event: ProcessEvent::Receive {
                sender: Pid::Node(node), message: ProductionWireMessage::StoreCall { op, .. },
            }, .. } = action { operations[*node as usize].insert(*op); }
        }
        assert!(operations[0].intersection(&operations[1]).next().is_some(), "node-local operation IDs must overlap safely");
    }
}

#[test]
fn production_fleet_drives_deadlines_through_real_wakes_and_store_operations() {
    use echod_logic::production_rover::{config_out, Pid, ProductionFleetConfig, ProductionWireMessage, ProductionEffectData, ProductionAnswerData};
    use rover_spec::rover::comm::{BoundaryEvent, ProcessEvent};
    use rover_exec::Action;
    let mut node = Config::memory("n1");
    node.timer_bucket_ms = 100;
    let config = ProductionFleetConfig { nodes: vec![config_out(&node)], loops: true, appendable: false, fault: None };
    let inputs = vec![
        (0, Pid::Node(0), fleet_request(1, "promise.create", json!({ "id": "clock:1", "timeoutAt": 120, "tags": {} }), 0)),
        (600, Pid::Node(0), fleet_request(2, "promise.get", json!({ "id": "clock:1" }), 600)),
    ];
    let execution = drive_fleet(&echod_logic::production_rover::FleetSpec, &config, inputs, vec![100, 200, 500], None, None);
    assert!(execution.certificate.iter().any(|action| matches!(action,
        Action::Process { process: Pid::Node(0), at, event: ProcessEvent::Timeout, .. } if *at > 0 && *at < 600)));
    assert!(execution.certificate.iter().any(|action| matches!(action,
        Action::Process { process: Pid::Store, at, event: ProcessEvent::Receive {
            message: ProductionWireMessage::StoreCall { request: StoreReq::PutIfMatch { key, .. }, .. }, ..
        }, .. } if key == "wf/clock" && *at > 0 && *at < 600)), "the timer must commit expiry before the later request");
    assert!(execution.trace.iter().any(|event| matches!(event,
        BoundaryEvent::Output { message: ProductionWireMessage::Effect(ProductionEffectData::Reply {
            id: 2, response: Ok(ProductionAnswerData::Step { response: echod_logic::verified::Response::Promise(r), .. }),
        }), .. } if r.status == 200 && r.promise.as_ref().is_some_and(|p|
            p.state == echod_logic::verified::PromiseState::RejectedTimedout))));
}

#[test]
fn public_admission_rejects_empty_heartbeat_before_document_routing() {
    let envelope = RequestEnvelope {
        kind: "task.heartbeat".into(),
        head: RequestHead { corr_id: "empty-heartbeat".into(), version: PROTOCOL_VERSION.into(), auth: None, debug_time: None },
        data: json!({"pid": "worker", "tasks": []}),
    };
    let Admission::Rejected(response) = admit::admit_before_staging(&envelope, 10, false) else {
        panic!("empty heartbeat has no routable document");
    };
    assert_eq!(response.head.status, 400);
    assert_eq!(response.head.corr_id, "empty-heartbeat");
}

#[test]
fn typed_public_routing_rejections_preserve_correlation_and_leave_node_unchanged() {
    use echod_logic::verified as rows;
    use echod_logic::production_rover::{config_out, PublicSpec, Pid, ProductionFleetConfig,
        ProductionPublicCall, ProductionWireMessage, ProductionAnswerData};
    use rover_exec::{Proc as _, Spec as _};
    use rover_spec::rover::comm::ProcessEvent;
    let config = ProductionFleetConfig {
        nodes: vec![config_out(&Config::memory("n1"))], loops: false, appendable: false, fault: None,
    };
    let (_, node) = PublicSpec.initial(&config).into_iter().find(|(pid, _)| *pid == Pid::Node(0)).unwrap();
    for (kind, data, request) in [
        ("task.heartbeat", json!({"pid": "worker", "tasks": []}),
            rows::Request::TaskHeartbeat(rows::TaskHeartbeatReq { pid: "worker".into(), tasks: vec![] })),
        ("promise.get", json!({"id": ":missing-origin"}),
            rows::Request::PromiseGet(rows::PromiseGetReq { id: ":missing-origin".into() })),
        ("schedule.get", json!({"id": ""}),
            rows::Request::ScheduleGet(rows::ScheduleGetReq { id: "".into() })),
    ] {
        let envelope = RequestEnvelope {
            kind: kind.into(),
            head: RequestHead { corr_id: "rejected:7".into(), version: PROTOCOL_VERSION.into(), auth: None, debug_time: None },
            data,
        };
        let Admission::Rejected(parsed) = admit::admit_before_staging(&envelope, 10, false) else { panic!("routing rejection"); };
        let call = ProductionPublicCall {
            client: "rejected".into(), id: 7, kind: kind.into(), corr: "rejected:7".into(),
            request, action_kind: None, now: 10, pinned: false,
        };
        let result = node.on_event(&config, 100, &ProcessEvent::Receive {
            sender: Pid::Outside, message: ProductionWireMessage::PublicRequest(call.clone()),
        }).remove(0);
        assert_eq!(result.state, node);
        assert_eq!(result.send.len(), 1);
        assert!(matches!(&result.send[0], (Pid::Outside, ProductionWireMessage::PublicResult {
            call: returned, response: Ok(ProductionAnswerData::Step {
                kind: returned_kind, corr, response: rows::Response::Status(status), why, ..
            }),
        }) if returned == &call && returned_kind == kind && corr == &parsed.head.corr_id
            && status.status == parsed.head.status as u16
            && why.as_deref() == Some("Request data does not name an id")));
    }
}

fn public_request(client: &str, id: u64, kind: &str, data: Value) -> echod_logic::production_rover::ProductionWireMessage {
    public_request_at(client, id, kind, data, 0, None)
}

fn public_request_at(client: &str, id: u64, kind: &str, data: Value, offered: u64, debug_time: Option<i64>)
    -> echod_logic::production_rover::ProductionWireMessage {
    use echod_logic::production_rover::{event_out, ProductionInput, ProductionPublicCall, ProductionWireMessage};
    let envelope = RequestEnvelope {
        kind: kind.into(),
        head: RequestHead { corr_id: format!("{client}:{id}"), version: PROTOCOL_VERSION.into(), auth: None, debug_time },
        data,
    };
    let Admission::Request(d) = admit::admit_before_staging(&envelope, offered, debug_time.is_some()) else { panic!("decoded protocol request"); };
    assert!(d.then.is_none());
    let ProductionInput::Request { call, .. } = event_out(Event::Request {
        clock: 0, request: RequestEvent::Protocol(Call { id, kind: d.kind, corr: d.corr, target: d.target,
            request: d.request, action_kind: d.action_kind, now: d.now, pinned: d.pinned, then: None }),
    }) else { unreachable!(); };
    ProductionWireMessage::PublicRequest(ProductionPublicCall {
        client: client.into(), id, kind: call.kind, corr: call.corr, request: call.request,
        action_kind: call.action_kind, now: call.now, pinned: call.pinned,
    })
}

#[test]
fn production_public_boundary_normalizes_requests_and_preserves_failure_correlation() {
    use echod_logic::production_rover::{config_out, protocol_observation, PublicSpec, Pid, ProductionFleetConfig,
        ProductionWireMessage, ProductionAnswerData, ProtocolMessage, ProtocolOutput};
    use rover_spec::rover::comm::BoundaryEvent;
    use rover_spec::rover::RoverSpec::Label;
    for failure in [None, Some(1), Some(2)] {
        let config = ProductionFleetConfig {
            nodes: vec![config_out(&Config::memory("n1")), config_out(&Config::memory("n2"))],
            loops: false, appendable: false, fault: Some("causal store failure".into()),
        };
        let detached = public_request("detached", 7, "task.fence", json!({
            "id": "a:missing", "version": 0,
            "action": { "kind": "promise.create", "head": {}, "data": { "id": "b:child", "timeoutAt": 10_000, "tags": {} } }
        }));
        assert!(matches!(&detached, ProductionWireMessage::PublicRequest(call)
            if matches!(call.request, echod_logic::verified::Request::TaskFence(_))));
        let inputs = vec![
            (0, Pid::Node(0), detached),
            (0, Pid::Node(0), public_request("reader", 7, "promise.get", json!({ "id": "b:child" }))),
            (0, Pid::Node(1), public_request("independent", 7, "promise.create", json!({ "id": "c:other", "timeoutAt": 10_000, "tags": {} }))),
        ];
        let execution = drive_fleet(&PublicSpec, &config, inputs, vec![], failure.map(|outcome| ("wf/b".into(), outcome)), None);
        let projected: Vec<_> = execution.trace.iter().flat_map(|event| {
            let label = match event {
                BoundaryEvent::Input { recipient, at, message } => Label::Input { recipient: *recipient, at: *at, message: message.clone() },
                BoundaryEvent::Output { sender, at, message } => Label::Outside { sender: *sender, at: *at, message: message.clone() },
                BoundaryEvent::Clock { at } => Label::Clock { at: *at },
            };
            protocol_observation(&label)
        }).map(|event| event.expect("every public observation belongs to the typed protocol")).collect();
        assert!(projected.iter().any(|event| matches!(event,
            BoundaryEvent::Input { message: ProtocolMessage::Request(call), .. }
                if call.call.client == "detached" && matches!(call.call.request, echod_logic::verified::Request::TaskFence(_)))));
        assert!(projected.iter().any(|event| matches!(event,
            BoundaryEvent::Output { message: ProtocolMessage::Output(ProtocolOutput::Response { client, id: 7,
                response: echod_logic::verified::Response::TaskFence(r) }), .. }
                if client == "detached" && r.status == if failure.is_some() { 503 } else { 404 })));
        let replies: Vec<_> = execution.trace.iter().filter_map(|event| match event {
            BoundaryEvent::Output { message: ProductionWireMessage::PublicResult { call, response }, .. } => Some((call, response)),
            _ => None,
        }).collect();
        assert_eq!(replies.len(), 3);
        for (call, response) in &replies {
            assert_eq!(call.id, 7);
            assert_eq!(call.corr, format!("{}:7", call.client));
            match call.client.as_str() {
                "detached" => {
                    assert_eq!(call.kind, "task.fence");
                    assert_eq!(call.action_kind.as_deref(), Some("promise.create"));
                    assert!(matches!(call.request, echod_logic::verified::Request::TaskFence(_)));
                    if failure.is_some() { assert_eq!(*response, &Err("store unavailable: causal store failure".into())); }
                    else { assert!(matches!(response, Ok(ProductionAnswerData::Step { kind, corr,
                        response: echod_logic::verified::Response::TaskFence(r), .. })
                        if kind == "task.fence" && corr == "detached:7" && r.status == 404)); }
                },
                "reader" => assert!(matches!(response, Ok(ProductionAnswerData::Step { kind, corr,
                    response: echod_logic::verified::Response::Promise(r), .. })
                    if kind == "promise.get" && corr == "reader:7" && r.status == if failure == Some(1) { 404 } else { 200 })),
                "independent" => assert!(matches!(response, Ok(ProductionAnswerData::Step { kind, corr,
                    response: echod_logic::verified::Response::Promise(r), .. })
                    if kind == "promise.create" && corr == "independent:7" && r.status == 200)),
                other => panic!("unexpected client {other}"),
            }
        }
    }
}

#[test]
fn production_public_time_keeps_transport_admission_and_document_clamp_separate() {
    use echod_logic::production_rover::{config_out, PublicSpec, Pid, ProductionFleetConfig, ProductionWireMessage, ProductionAnswerData};
    use rover_spec::rover::comm::BoundaryEvent;
    let mut node = Config::memory("n1");
    node.debug = true;
    let config = ProductionFleetConfig { nodes: vec![config_out(&node)], loops: false, appendable: false, fault: None };
    let inputs = vec![
        (100, Pid::Node(0), public_request_at("seed", 1, "promise.create",
            json!({ "id": "clock:seed", "timeoutAt": 10_000, "tags": {} }), 100, Some(7))),
        (200, Pid::Node(0), public_request_at("anchor", 2, "promise.create",
            json!({ "id": "clock:anchor", "timeoutAt": 10_000, "tags": {} }), 200, Some(20))),
        (200, Pid::Node(0), public_request_at("queued", 3, "promise.create",
            json!({ "id": "clock:queued", "timeoutAt": 10_000, "tags": {} }), 200, Some(7))),
    ];
    let execution = drive_fleet(&PublicSpec, &config, inputs, vec![], None, None);
    let created: Vec<_> = execution.trace.iter().filter_map(|event| match event {
        BoundaryEvent::Output { at, message: ProductionWireMessage::PublicResult { call, response:
            Ok(ProductionAnswerData::Step { response: echod_logic::verified::Response::Promise(r), .. }) }, .. } =>
            Some((call.client.as_str(), call.now, *at, r.promise.as_ref().unwrap().created_at)),
        _ => None,
    }).collect();
    assert_eq!(created, vec![("seed", 7, 100, 7), ("anchor", 20, 200, 20), ("queued", 7, 200, 20)]);
}

#[test]
fn production_public_unpinned_time_uses_the_observed_fleet_floor() {
    use echod_logic::production_rover::{config_out, PublicSpec, Pid, ProductionFleetConfig, ProductionWireMessage, ProductionAnswerData};
    use rover_spec::rover::comm::BoundaryEvent;
    let mut node = Config::memory("n1");
    node.heartbeat_ms = 20;
    let mut other = Config::memory("n2");
    other.heartbeat_ms = 20;
    let config = ProductionFleetConfig { nodes: vec![config_out(&node), config_out(&other)], loops: true, appendable: false, fault: None };
    let origin = (0..100).map(|i| format!("floor{i}")).find(|o| echod_logic::verified::node::fnv1a(o) % 2 == 1).unwrap();
    let inputs = vec![(100, Pid::Node(1), public_request_at("delayed", 1, "promise.create",
        json!({ "id": format!("{origin}:1"), "timeoutAt": 10_000, "tags": {} }), 7, None))];
    let execution = drive_fleet(&PublicSpec, &config, inputs, vec![20], None, None);
    let observed: Vec<_> = execution.trace.iter().filter_map(|event| match event {
        BoundaryEvent::Output { at, message: ProductionWireMessage::PublicResult { call, response:
            Ok(ProductionAnswerData::Step { response: echod_logic::verified::Response::Promise(r), .. }) }, .. } =>
                Some((*at, call.now, call.pinned, r.promise.as_ref().map(|p| p.created_at))),
        _ => None,
    }).collect();
    assert_eq!(observed, vec![(100, 7, false, Some(20))]);
}

#[test]
fn production_public_retry_reclamps_saved_time_to_the_reread_document() {
    check_public_retry_reclamps("n1");
}

#[test]
fn seeded_operation_wrap_can_accept_a_replayed_absent_read() {
    let mut reader = Harness::new("reader");
    reader.start(false);
    let old_op = reader.state.next_op;
    assert_eq!(reader.request("promise.get", json!({"id": "old:missing"})).0, 404);
    assert_eq!(reader.state.next_op, old_op + 1);

    let mut writer = Harness::new("writer");
    writer.start(false);
    assert_eq!(writer.request("promise.create", json!({
        "id": "target:live", "timeoutAt": 2_000_000, "tags": {}
    })).0, 200);
    reader.bucket.objects.extend(writer.bucket.objects);

    // Seed only the allocator boundary; this does not establish a reachable
    // execution prefix containing 2^64 operations.
    reader.state.next_op = u64::MAX;
    for i in 0..=old_op {
        assert_eq!(reader.request("promise.get", json!({"id": format!("gap{i}:missing")})).0, 404);
    }
    assert_eq!(reader.state.next_op, old_op);
    let envelope = RequestEnvelope {
        kind: "promise.get".into(),
        head: RequestHead { corr_id: "new-read".into(), version: PROTOCOL_VERSION.into(), auth: None, debug_time: None },
        data: json!({"id": "target:live"}),
    };
    let Admission::Request(d) = admit::admit(&envelope, reader.clock, false) else { panic!("valid read"); };
    let issued = reader.step(Event::Request {
        clock: reader.clock,
        request: RequestEvent::Protocol(Call {
            id: 999, kind: d.kind, corr: d.corr, target: d.target, request: d.request,
            action_kind: d.action_kind, now: d.now, pinned: d.pinned, then: d.then,
        }),
    });
    let request = issued.into_iter().find_map(|effect| match effect {
        Effect::Store { op, request } if op == old_op => Some(request),
        _ => None,
    }).unwrap();
    assert!(matches!(&request, StoreReq::Get { key } if key == "wf/target"));
    let fresh = reader.bucket.call(request);
    assert!(matches!(&fresh, StoreRes::Get { result: Ok(Some(_)) }));

    let stale = reader.step(Event::Store { clock: reader.clock, op: old_op, response: StoreRes::Get { result: Ok(None) } });
    assert!(stale.iter().any(|effect| matches!(effect,
        Effect::Reply { id: 999, response: Ok(echod_logic::Answer::Step { corr, response: echod_logic::verified::Response::Promise(r), .. }) }
            if corr == "new-read" && r.status == 404)));
    let late = reader.step(Event::Store { clock: reader.clock, op: old_op, response: fresh });
    assert!(!late.iter().any(|effect| matches!(effect, Effect::Reply { id: 999, .. })));
}

#[test]
fn production_public_retry_with_distinct_node_ids_reclamps_after_cas_conflict() {
    check_public_retry_reclamps("n2");
}

fn check_public_retry_reclamps(second_node_id: &str) {
    use echod_logic::production_rover::{config_out, PublicSpec, Pid, ProductionFleetConfig, ProductionWireMessage, ProductionAnswerData};
    use rover_spec::rover::comm::{BoundaryEvent, ProcessEvent};
    use rover_exec::Action;
    let mut node = Config::memory("n1");
    node.debug = true;
    let mut other = Config::memory(second_node_id);
    other.debug = true;
    let config = ProductionFleetConfig {
        nodes: vec![config_out(&node), config_out(&other)],
        loops: false, appendable: false, fault: None,
    };
    let inputs = vec![
        (0, Pid::Node(0), public_request_at("seed", 1, "promise.create",
            json!({ "id": "clock:seed", "timeoutAt": 10_000, "tags": {} }), 0, Some(20))),
        (100, Pid::Node(0), public_request_at("retry", 2, "promise.create",
            json!({ "id": "clock:retry", "timeoutAt": 10_000, "tags": {} }), 100, Some(7))),
        (200, Pid::Node(1), public_request_at("racer", 3, "promise.create",
            json!({ "id": "clock:racer", "timeoutAt": 10_000, "tags": {} }), 200, Some(30))),
    ];
    let execution = drive_fleet(&PublicSpec, &config, inputs, vec![], None, Some((Pid::Node(0), "wf/clock".into(), "racer".into())));
    let proposed: Vec<_> = execution.certificate.iter().filter_map(|action| match action {
        Action::Process { process: Pid::Store, event: ProcessEvent::Receive { sender: Pid::Node(0),
            message: ProductionWireMessage::StoreCall { request: StoreReq::PutIfMatch { key, body, .. }, .. } }, .. } if key == "wf/clock" => {
                let loaded = echod_logic::document::decode_workflow(body).unwrap();
                Some(echod_logic::document::loaded_committed_at(&loaded))
            },
        _ => None,
    }).collect();
    assert_eq!(proposed, vec![20, 30]);
    assert!(execution.certificate.iter().any(|action| matches!(action,
        Action::Process { process: Pid::Node(0), event: ProcessEvent::Receive {
            message: ProductionWireMessage::StoreReply { response: StoreRes::PutIfMatch {
                result: Err(echod_logic::types::StoreError::PreconditionFailed),
            }, .. }, .. }, .. })));
    assert!(execution.trace.iter().any(|event| matches!(event,
        BoundaryEvent::Output { message: ProductionWireMessage::PublicResult { call, response:
            Ok(ProductionAnswerData::Step { response: echod_logic::verified::Response::Promise(r), .. }) }, .. }
        if call.client == "retry" && call.now == 7 && r.promise.as_ref().is_some_and(|p| p.created_at == 30))));
}

#[test]
fn production_rover_certifies_detached_create_with_concurrent_document_flights() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    let far = h.clock + 10_000;
    assert_eq!(h.request("promise.create", json!({ "id": "b:seed", "timeoutAt": far + 10_000, "tags": {} })).0, 200);
    let before_destination = h.bucket.objects["wf/b"].0.clone();
    let (fence, mut destination) = h.submit_held("task.fence", json!({
        "id": "a:missing", "version": 0,
        "action": { "kind": "promise.create", "head": {}, "data": { "id": "b:child", "timeoutAt": far, "tags": {} } }
    }));
    let (independent, other) = h.submit_held("promise.create", json!({ "id": "c:other", "timeoutAt": far, "tags": {} }));
    let (queued, waiting) = h.submit_held("promise.get", json!({ "id": "b:child" }));
    assert_eq!(destination.len(), 1);
    assert_eq!(other.len(), 1);
    assert!(waiting.is_empty());
    let (op, request) = destination.pop().unwrap();
    assert!(matches!(&request, StoreReq::GetIfNoneMatch { key, .. } if key == "wf/b"));
    let response = h.bucket.call(request);
    let mut timer = h.answer_held(op, response);
    assert_eq!(timer.len(), 1);
    let (op, request) = timer.pop().unwrap();
    assert!(matches!(&request, StoreReq::Put { key, .. } if key.starts_with("t/")));
    let response = h.bucket.call(request);
    let mut commit = h.answer_held(op, response);
    assert_eq!(commit.len(), 1);
    assert!(matches!(&commit[0].1, StoreReq::PutIfMatch { key, .. } if key == "wf/b"));
    h.perform_all(other.into_iter().map(|(op, request)| Effect::Store { op, request }).collect());
    assert_eq!(h.take(independent).0, 200);
    assert!(!h.replies.iter().any(|(id, _)| *id == fence || *id == queued));
    assert_eq!(h.bucket.objects["wf/b"].0, before_destination);
    let (op, request) = commit.pop().unwrap();
    let response = h.bucket.call(request);
    let mut removal = h.answer_held(op, response);
    assert_ne!(h.bucket.objects["wf/b"].0, before_destination);
    assert_eq!(removal.len(), 1);
    let (op, request) = removal.pop().unwrap();
    assert!(matches!(&request, StoreReq::Del { key } if key.starts_with("t/")));
    assert!(!h.replies.iter().any(|(id, _)| *id == fence || *id == queued));
    let following = h.answer_held(op, StoreRes::Del {
        result: Err(echod_logic::types::StoreError::Unavailable("timer removal failed".into())),
    });
    assert!(following.iter().any(|(_, request)| matches!(request, StoreReq::Get { key } if key == "wf/a")));
    h.perform_all(following.into_iter().map(|(op, request)| Effect::Store { op, request }).collect());
    let (_, answer) = h.replies.iter().find(|(id, _)| *id == fence).unwrap();
    assert!(matches!(answer, Ok(echod_logic::Answer::Step { kind, corr, action_kind, response, .. })
        if kind == "task.fence" && corr == &format!("c{fence}") && action_kind.as_deref() == Some("promise.create")
        && matches!(response, echod_logic::verified::Response::TaskFence(r) if r.status == 404 && r.action.is_none())));
    for (id, expected) in [(fence, 404), (queued, 200)] {
        let answer = h.replies.iter().find(|(rid, _)| *rid == id).unwrap().1.as_ref().unwrap();
        assert_eq!(codec::envelope(answer).head.status, expected);
    }
    assert!(h.bucket.objects.contains_key("wf/b"));
    certify_recorded_production(&h);
}

#[test]
fn same_document_requests_queue_until_the_first_commit_finishes() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    let (create, mut calls) = h.submit_held("promise.create", json!({ "id": "a:1", "timeoutAt": h.clock + 600 }));
    let (get, queued) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    assert_eq!(calls.len(), 1);
    assert!(queued.is_empty());
    while h.replies.is_empty() {
        assert_eq!(calls.len(), 1);
        let (op, request) = calls.pop().unwrap();
        let response = h.bucket.call(request);
        calls = h.answer_held(op, response);
    }
    assert_eq!(h.take(create).0, 200);
    assert_eq!(calls.len(), 1, "the next lane request starts only after commit");
    let (op, request) = calls.pop().unwrap();
    assert!(matches!(request, StoreReq::GetIfNoneMatch { .. }));
    let response = h.bucket.call(request);
    assert!(h.answer_held(op, response).is_empty());
    assert_eq!(h.take(get).0, 200);
}

#[test]
fn notifications_wait_for_cas_and_best_effort_timer_removal() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    assert_eq!(h.request("promise.create", json!({
        "id": "a:1", "timeoutAt": h.clock + 600,
        "tags": { "resonate:target": "http://worker/" },
    })).0, 200);
    assert!(h.sent.is_empty(), "create does not perform a post-handler sweep");
    let (id, mut calls) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    let (read_op, read) = calls.pop().unwrap();
    assert!(matches!(read, StoreReq::GetIfNoneMatch { .. }));
    let response = h.bucket.call(read);
    calls = h.answer_held(read_op, response);
    assert_eq!(calls.len(), 1);
    let (timer_op, timer) = calls.pop().unwrap();
    assert!(matches!(&timer, StoreReq::Put { key, .. } if key.starts_with("t/")));
    assert!(h.sent.is_empty());
    let response = h.bucket.call(timer);
    calls = h.answer_held(timer_op, response);
    assert_eq!(calls.len(), 1);
    let (write_op, write) = calls.pop().unwrap();
    assert!(matches!(write, StoreReq::PutIfMatch { .. }));
    assert!(h.sent.is_empty());
    let response = h.bucket.call(write);
    calls = h.answer_held(write_op, response);
    assert_eq!(calls.len(), 1);
    let (delete_op, delete) = calls.pop().unwrap();
    let StoreReq::Del { key } = delete else { panic!("expected old timer removal") };
    assert!(h.sent.is_empty(), "a held deletion reply still blocks completion");
    assert!(h.replies.is_empty());
    let failed = StoreRes::Del {
        result: Err(echod_logic::types::StoreError::Unavailable("delete failed".into())),
    };
    assert!(h.answer_held(delete_op, failed).is_empty());
    assert!(h.bucket.objects.contains_key(&key), "failed deletion leaves the timer");
    assert_eq!(h.sent.len(), 1);
    assert!(h.sent[0].contains("execute a:1"));
    assert_eq!(h.take(id).0, 200);
    assert_eq!(h.request("promise.get", json!({ "id": "a:1" })).0, 200);
    assert_eq!(h.sent.len(), 1);
}

#[test]
fn failed_cas_discards_notifications_and_reloads_before_retry() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    assert_eq!(h.request("promise.create", json!({
        "id": "a:1", "timeoutAt": h.clock + 600,
        "tags": { "resonate:target": "http://worker/" },
    })).0, 200);
    let (id, mut calls) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    let (read_op, read) = calls.pop().unwrap();
    let response = h.bucket.call(read);
    calls = h.answer_held(read_op, response);
    let (timer_op, timer) = calls.pop().unwrap();
    assert!(matches!(timer, StoreReq::Put { .. }));
    let response = h.bucket.call(timer);
    calls = h.answer_held(timer_op, response);
    let (write_op, write) = calls.pop().unwrap();
    assert!(matches!(write, StoreReq::PutIfMatch { .. }));
    let probe = h.replay_probe.as_ref().unwrap();
    let mut branch_bucket = Bucket { objects: h.bucket.objects.clone() };
    let successful = branch_bucket.call(write.clone());
    let success_event = Event::Store { op: write_op, response: successful, clock: h.clock };
    let failure_event = Event::Store {
        op: write_op,
        response: StoreRes::PutIfMatch {
            result: Err(echod_logic::types::StoreError::PreconditionFailed),
        },
        clock: h.clock,
    };
    let (_, success_effects) = echod_logic::replay::replay_step(
        probe.config.clone(), probe.loops, &probe.history, echod_logic::replay::copy_event(&success_event));
    let (_, failure_effects) = echod_logic::replay::replay_step(
        probe.config.clone(), probe.loops, &probe.history, failure_event);
    assert!(success_effects != failure_effects);
    let (_, success_again) = echod_logic::replay::replay_step(
        probe.config.clone(), probe.loops, &probe.history, success_event);
    assert!(success_effects == success_again, "the failed branch must not mutate the shared prefix");
    calls = h.answer_held(write_op, StoreRes::PutIfMatch {
        result: Err(echod_logic::types::StoreError::PreconditionFailed),
    });
    assert!(h.sent.is_empty());
    assert!(h.replies.is_empty());
    assert_eq!(calls.len(), 1);
    assert!(matches!(&calls[0].1, StoreReq::Get { .. }), "retry must read fresh data");
    while !calls.is_empty() {
        assert_eq!(calls.len(), 1);
        let (op, request) = calls.pop().unwrap();
        let response = h.bucket.call(request);
        calls = h.answer_held(op, response);
    }
    assert_eq!(h.sent.len(), 1);
    assert_eq!(h.take(id).0, 200);
}

#[test]
fn failed_timer_add_prevents_document_write_and_notifications() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    assert_eq!(h.request("promise.create", json!({
        "id": "a:1", "timeoutAt": h.clock + 600,
        "tags": { "resonate:target": "http://worker/" },
    })).0, 200);
    let (id, mut calls) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    let (read_op, read) = calls.pop().unwrap();
    let response = h.bucket.call(read);
    calls = h.answer_held(read_op, response);
    assert_eq!(calls.len(), 1);
    let (timer_op, timer) = calls.pop().unwrap();
    assert!(matches!(timer, StoreReq::Put { .. }));
    let calls = h.answer_held(timer_op, StoreRes::Put {
        result: Err(echod_logic::types::StoreError::Unavailable("timer put failed".into())),
    });
    assert!(calls.is_empty(), "a failed timer add must not issue a document CAS");
    assert!(h.sent.is_empty());
    let (reply_id, response) = h.replies.pop().unwrap();
    assert_eq!(reply_id, id);
    assert!(response.is_err());
}

#[test]
fn exhausted_cas_retries_release_the_document_lane_without_notifications() {
    let mut h = Harness::replay_checked("n1");
    h.start(false);
    assert_eq!(h.request("promise.create", json!({
        "id": "a:1", "timeoutAt": h.clock + 600,
        "tags": { "resonate:target": "http://worker/" },
    })).0, 200);
    let (first, mut calls) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    let (second, queued) = h.submit_held("promise.get", json!({ "id": "a:1" }));
    assert!(queued.is_empty());
    let mut attempts = 0;
    while h.replies.is_empty() {
        assert_eq!(calls.len(), 1);
        let (op, request) = calls.pop().unwrap();
        let response = match request {
            StoreReq::PutIfMatch { .. } => {
                attempts += 1;
                assert!(attempts <= 9);
                StoreRes::PutIfMatch { result: Err(echod_logic::types::StoreError::PreconditionFailed) }
            },
            other => h.bucket.call(other),
        };
        calls = h.answer_held(op, response);
        assert!(h.sent.is_empty());
    }
    assert_eq!(attempts, 9);
    let (reply_id, response) = h.replies.pop().unwrap();
    assert_eq!(reply_id, first);
    assert!(response.is_err());
    assert_eq!(calls.len(), 1, "the queued request starts after retry exhaustion");
    while !calls.is_empty() {
        assert_eq!(calls.len(), 1);
        let (op, request) = calls.pop().unwrap();
        let response = h.bucket.call(request);
        calls = h.answer_held(op, response);
    }
    assert_eq!(h.take(second).0, 200);
    assert_eq!(h.sent.len(), 1);
}

#[test]
fn a_promise_is_created_timed_out_and_the_key_collected() {
    let mut h = Harness::replay_checked("n1");
    h.start(true);
    // announced; the configuration naming this node is written by the
    // first refresh and read by the next heartbeat
    assert_eq!(h.keys("nodes/"), vec!["nodes/n1".to_string()]);
    assert!(!h.state.acting(), "no configuration read yet");
    h.advance(100);
    assert!(h.state.acting(), "one node, one member, fresh");
    assert_eq!(h.state.membership().members, vec!["n1".to_string()]);
    assert!(h.wake_after.is_some(), "the heartbeat is scheduled");

    // a promise with a deadline: a document, and a key put before it
    let (status, data) = h.request("promise.create", json!({ "id": "a:1", "timeoutAt": h.clock + 500, "tags": { "resonate:scope": "global" } }));
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["promise"]["state"], "pending");
    assert_eq!(h.keys("wf/").len(), 1);
    assert_eq!(h.keys("t/").len(), 1, "one deadline key");
    let (status, data) = h.request("promise.get", json!({ "id": "a:1" }));
    assert_eq!(status, 200);
    assert_eq!(data["promise"]["state"], "pending");
    assert!(h.notes.iter().any(|n| matches!(n, Note::Cache(echod_logic::types::CacheResult::Revalidated))), "the second load revalidated the cache");

    // a listener, then the deadline: the sweep rejects the promise and
    // the listener hears of it
    let (status, _) = h.request("promise.register_listener", json!({ "awaited": "a:1", "address": "http://worker/" }));
    assert_eq!(status, 200);
    h.advance(600);
    let (status, data) = h.request("promise.get", json!({ "id": "a:1" }));
    assert_eq!(status, 200);
    assert_eq!(data["promise"]["state"], "rejected_timedout", "{data}");
    assert!(h.notes.iter().any(|n| matches!(n, Note::Sweep(SweepOutcome::Fired))));
    assert_eq!(h.sent.len(), 1, "one unblock: {:?}", h.sent);
    assert!(h.sent[0].starts_with("http://worker/ "));
    assert!(h.keys("t/").is_empty(), "the fired key was collected");
}

#[test]
fn a_schedule_fires_into_its_origin() {
    let mut h = Harness::new("n1");
    h.start(true);
    h.advance(100);
    let (status, data) = h.request("schedule.create", json!({ "id": "tick", "cron": "* * * * * *", "promiseId": "tick-{{.timestamp}}", "promiseTimeout": 60_000, "promiseTags": { "resonate:target": "http://worker/" } }));
    assert_eq!(status, 200, "{data}");
    assert_eq!(h.keys("sched/").len(), 1);
    assert_eq!(h.keys("t/").len(), 1, "the next run has a key");
    h.advance(1_100);
    assert!(h.notes.iter().any(|n| matches!(n, Note::FireBegin { .. })), "the schedule fired");
    assert!(h.notes.iter().any(|n| matches!(n, Note::AdvanceEnd { committed: true, .. })));
    assert_eq!(h.sent.len(), 1, "the occurrence's task was offered: {:?}", h.sent);
    let (status, data) = h.request("schedule.get", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    assert!(data["schedule"]["lastRunAt"].is_number(), "{data}");
    assert_eq!(h.keys("t/").len(), 2, "the occurrence's deadline and the next run: {:?}", h.keys("t/"));
    let (status, _) = h.request("schedule.delete", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    let (status, _) = h.request("schedule.get", json!({ "id": "tick" }));
    assert_eq!(status, 404);
}

/// A bucket is listed ahead of the clock, and again once the clock has left
/// it: a key another node armed into it in between, for a target this node
/// owns, is found then rather than at the next membership change.
#[test]
fn a_bucket_is_listed_again_once_the_clock_leaves_it() {
    let mut h = Harness::new("n1");
    h.start(true);
    h.advance(100);
    let bucket_ms = 1_000; // the harness's `timer_bucket_ms`
    let current = h.clock - h.clock % bucket_ms;
    let listed = |h: &Harness, b: u64| h.notes.iter().filter(|n| matches!(n, Note::BucketLoaded { bucket, .. } if *bucket == b)).count();
    // the full load reached the next bucket; nothing more while the clock
    // stays in this one
    h.advance(bucket_ms / 2);
    assert_eq!(listed(&h, current), 0);
    // the clock leaves the bucket: it is listed once more, and the horizon
    // moves on by one
    h.advance(bucket_ms / 2 + 10);
    assert_eq!(listed(&h, current), 1, "the bucket just closed is listed again");
    assert_eq!(listed(&h, current + 2 * bucket_ms), 1, "and the horizon moved on");
}

/// A schedule deleted and created again under the same id fires again: the
/// new document's next run gets a key of its own, whatever key the old one
/// left behind.
#[test]
fn a_schedule_recreated_after_its_delete_fires_again() {
    let mut h = Harness::new("n1");
    h.start(true);
    h.advance(100);
    let (status, _) = h.request("schedule.create", json!({ "id": "tick", "cron": "*/2 * * * * *", "promiseId": "tick-{{.timestamp}}", "promiseTimeout": 60_000, "promiseTags": { "resonate:target": "http://worker/" } }));
    assert_eq!(status, 200);
    let (status, _) = h.request("schedule.delete", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    h.advance(300);
    let fired = h.notes.iter().filter(|n| matches!(n, Note::FireBegin { .. })).count();
    assert_eq!(fired, 0, "a deleted schedule does not fire");
    let (status, data) = h.request("schedule.create", json!({ "id": "tick", "cron": "*/2 * * * * *", "promiseId": "tock-{{.timestamp}}", "promiseTimeout": 60_000, "promiseTags": { "resonate:target": "http://worker/" } }));
    assert_eq!(status, 200, "{data}");
    let next = data["schedule"]["nextRunAt"].as_u64().unwrap();
    h.advance(next - h.clock + 100);
    h.advance(2_100);
    assert!(h.notes.iter().any(|n| matches!(n, Note::FireBegin { .. })), "the recreated schedule fired; keys {:?}", h.keys("t/"));
    let (status, data) = h.request("schedule.get", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    assert!(data["schedule"]["lastRunAt"].is_number(), "{data}");
}

#[test]
fn the_same_events_give_the_same_effects() {
    let run = || {
        let mut h = Harness::new("n1");
        h.start(true);
        h.advance(100);
        h.request("promise.create", json!({ "id": "a:1", "timeoutAt": h.clock + 500, "tags": { "resonate:scope": "global" } }));
        h.advance(600);
        h.bucket.objects.keys().cloned().collect::<Vec<_>>()
    };
    assert_eq!(run(), run());
}

#[test]
fn the_debug_operations_own_the_clock() {
    let mut h = Harness::new("n1");
    h.state = State::new({
        let mut cfg = Config::memory("n1");
        cfg.debug = true;
        cfg
    });
    h.start(false);
    let far = h.clock + 10_000;
    let (status, _) = h.request("promise.create", json!({ "id": "a:1", "timeoutAt": far, "tags": { "resonate:scope": "global" } }));
    assert_eq!(status, 200);
    let (status, _) = h.request("promise.register_listener", json!({ "awaited": "a:1", "address": "http://worker/" }));
    assert_eq!(status, 200);

    // the snapshot: the promise, its deadline, its listener
    let (status, snap) = h.request("debug.snap", json!({}));
    assert_eq!(status, 200, "{snap}");
    assert_eq!(snap["promises"].as_array().map(Vec::len), Some(1));
    assert_eq!(snap["promiseTimeouts"][0]["timeout"].as_u64(), Some(far));
    assert_eq!(snap["listeners"][0]["id"], "a:1");
    assert_eq!(snap["tasks"].as_array().map(Vec::len), Some(0));

    // the tick: time moves, the sweep runs, the listener hears
    let (status, data) = h.request("debug.tick", json!({ "time": far + 1 }));
    assert_eq!(status, 200, "{data}");
    let (_, snap) = h.request("debug.snap", json!({}));
    assert_eq!(snap["promises"][0]["state"], "rejected_timedout", "{snap}");
    assert!(snap["promiseTimeouts"].as_array().is_some_and(Vec::is_empty));
    assert_eq!(h.sent.len(), 1, "{:?}", h.sent);

    // the reset: nothing left
    let (status, _) = h.request("debug.reset", json!({}));
    assert_eq!(status, 200);
    assert!(h.keys("wf/").is_empty());
    let (status, _) = h.request("promise.get", json!({ "id": "a:1" }));
    assert_eq!(status, 404);
    let (_, snap) = h.request("debug.snap", json!({}));
    assert!(snap["promises"].as_array().is_some_and(Vec::is_empty));
}

/// A fence whose create targets another origin: the create commits first, on
/// its own document, then the fence's check on the task's. A stale fence
/// still leaves the promise created, and answers its 409; a settle in
/// another origin is refused outright.
#[test]
fn a_detached_create_lands_before_the_fence_is_checked() {
    let mut h = Harness::new("n1");
    h.start(true);
    h.advance(100);
    let far = h.clock + 100_000;
    let (status, _) = h.request("promise.create", json!({ "id": "a:t", "timeoutAt": far, "tags": { "resonate:target": "poll://w" } }));
    assert_eq!(status, 200);
    let (status, data) = h.request("task.acquire", json!({ "id": "a:t", "version": 0, "pid": "w", "ttl": 60_000 }));
    assert_eq!(status, 200, "{data}");
    let create = |id: &str| json!({ "kind": "promise.create", "head": {}, "data": { "id": id, "timeoutAt": far, "tags": {} } });

    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 9, "action": create("d:x") }));
    assert_eq!(status, 409, "{data}");
    assert_eq!(data, json!("Version mismatch"));
    let (status, data) = h.request("promise.get", json!({ "id": "d:x" }));
    assert_eq!(status, 200, "a stale detached create still lands: {data}");
    assert_eq!(data["promise"]["state"], "pending");

    let (status, data) = h.request("task.fence", json!({ "id": "a:ghost", "version": 0, "action": create("d:y") }));
    assert_eq!(status, 404, "{data}");
    let (status, _) = h.request("promise.get", json!({ "id": "d:y" }));
    assert_eq!(status, 200, "a detached create from a missing task lands too");

    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 1, "action": create("d:z") }));
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["action"]["head"]["status"], 200);
    assert_eq!(data["action"]["data"]["promise"]["id"], "d:z");
    assert_eq!(data["preload"], json!([]));
    assert_eq!(h.keys("wf/").len(), 2, "two origins' documents: {:?}", h.keys("wf/"));

    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 9, "action": create("a:n") }));
    assert_eq!(status, 409, "{data}");
    let (status, _) = h.request("promise.get", json!({ "id": "a:n" }));
    assert_eq!(status, 404, "a same-origin stale fence creates nothing");

    let settle = json!({ "kind": "promise.settle", "head": {}, "data": { "id": "d:z", "state": "resolved", "value": {} } });
    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 1, "action": settle }));
    assert_eq!(status, 400, "{data}");
    assert_eq!(data, json!("Action must belong to the task's origin"));
}

#[test]
fn admission_rejects_protocol_bounds_before_any_core_effect() {
    let mut h = Harness::new("n1");
    let max = echod_logic::verified::MAX_TIME;

    let (status, _) = h.request(
        "promise.create",
        json!({ "id": "a:too-late", "timeoutAt": max + 1, "tags": {} }),
    );
    assert_eq!(status, 400);

    for ttl in [0, max + 1] {
        let (status, _) = h.request(
            "task.acquire",
            json!({ "id": "a:task", "version": 0, "pid": "worker", "ttl": ttl }),
        );
        assert_eq!(status, 400);
    }

    let (status, _) = h.request(
        "schedule.create",
        json!({
            "id": "tick",
            "cron": "* * * * * *",
            "promiseId": "tick-{{.timestamp}}",
            "promiseTimeout": max,
            "promiseTags": {}
        }),
    );
    assert_eq!(status, 400);

    let action = json!({
        "kind": "promise.create",
        "head": {},
        "data": { "id": "detached:x", "timeoutAt": max + 1, "tags": {} }
    });
    let (status, _) = h.request(
        "task.fence",
        json!({ "id": "a:task", "version": 0, "action": action }),
    );
    assert_eq!(status, 400);

    assert!(h.bucket.objects.is_empty());
    assert!(h.sent.is_empty());
    assert!(h.notes.is_empty());
    assert!(h.wake_after.is_none());
}
