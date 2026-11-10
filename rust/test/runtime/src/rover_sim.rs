//! Isolated executable-Rover experiment over the production concrete machine.
//!
//! This does not participate in the synchronous DST in [`crate::sim`].  It
//! supplies the small adapter that `echod-process` deliberately keeps behind
//! its own `cfg(test)`, drives [`echod_rover_exec::exec`], and projects the
//! concrete boundary onto the public abstract Rover boundary for checking.
//! It exercises fixed multi-node fleets, concurrent seeded clients, all
//! request families, schedules, reordered delivery, and virtual time. Dynamic
//! membership, lifecycle changes, clock skew, and synthetic store failures
//! remain outside the concrete model.

use std::collections::{BTreeMap, BTreeSet};

use echod_logic::concrete::document::Node;
use echod_logic::concrete::model::{Fleet, Message as ConcreteMessage, Pid as ConcretePid};
use echod_logic::concrete::store::Store;
use echod_rover::rover::comm::{BoundaryEvent, ProcessEvent};
use echod_rover_exec::{
    check, exec, Action, Certificate, CheckConfig, Driver, ExecError, Proc, ProcResult, Spec,
    Strategy,
};
use echod_types::{Request, Response};
use rover_abstract_exec::{history_rank, RoverAbstractExec};
use rover_abstract_spec::model::Pid as AbstractPid;
use rover_abstract_spec::{Call, Message as AbstractMessage, Output, ServerConfig};
use rover_concrete_spec::model::{LocalV as ConcreteLocalV, RoverConcreteSpec, RETRY_TIMEOUT};
use rover_concrete_spec::{StoreCall, StoreError, StoreOutcome};
use vstd::prelude::View;

use crate::rng::Rng;
use crate::workload::{target_of, Generator, Seen};

pub type ConcreteTrace = Vec<BoundaryEvent<ConcretePid, ConcreteMessage>>;
pub type ConcreteCertificate = Certificate<ConcretePid, ConcreteMessage>;
pub type AbstractTrace = Vec<BoundaryEvent<AbstractPid, AbstractMessage>>;
pub type AbstractCertificate = Certificate<AbstractPid, AbstractMessage>;

/// Production node/store state wrapped locally so the external executable
/// trait can name the concrete mathematical state.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ConcreteProcess {
    Node(Node),
    Store(Store),
}

impl View for ConcreteProcess {
    type V = ConcreteLocalV;
}

impl Proc for ConcreteProcess {
    type Spec = ConcreteLocalV;

    fn on_event(
        &self,
        _config: &Fleet,
        now: u64,
        event: &ProcessEvent<ConcretePid, ConcreteMessage>,
    ) -> Vec<ProcResult<Self>> {
        match self {
            Self::Node(node) => node
                .step(now, event)
                .into_iter()
                .map(|(node, send)| ProcResult {
                    state: Self::Node(node),
                    send,
                    marks: Vec::new(),
                })
                .collect(),
            Self::Store(store) => store
                .step(event)
                .into_iter()
                .map(|(store, send)| ProcResult {
                    state: Self::Store(store),
                    send,
                    marks: Vec::new(),
                })
                .collect(),
        }
    }
}

/// Executable realization of `RoverConcreteSpec`, backed by production state.
struct RoverConcreteExecAdapter;

impl Spec for RoverConcreteExecAdapter {
    type Spec = RoverConcreteSpec;
    type Proc = ConcreteProcess;

    fn outside(&self) -> ConcretePid {
        ConcretePid::Outside
    }

    fn initial(&self, config: &Fleet) -> Vec<(ConcretePid, ConcreteProcess)> {
        let mut process = (0..config.nodes)
            .map(|id| {
                (
                    ConcretePid::Node(id),
                    ConcreteProcess::Node(Node::new(
                        id,
                        config.nodes,
                        config.loops,
                        config.retry_timeout,
                    )),
                )
            })
            .collect::<Vec<_>>();
        process.push((
            ConcretePid::Store,
            ConcreteProcess::Store(Store::empty(config.appendable)),
        ));
        process
    }

    fn injectable(&self, _config: &Fleet, message: &ConcreteMessage) -> bool {
        matches!(message, ConcreteMessage::Request(_) | ConcreteMessage::Stop)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionError {
    pub index: usize,
    pub reason: &'static str,
}

/// Explicitly erase the concrete topology at the external boundary.
///
/// Concrete inputs target a selected node and concrete outputs name that
/// node.  The abstract model has one `Service` process.  Calls and outputs
/// are already shared protocol values, so only the PID and message wrappers
/// need translation.  Store traffic is rejected because it is not a valid
/// external observation.
pub fn project(
    trace: &[BoundaryEvent<ConcretePid, ConcreteMessage>],
) -> Result<AbstractTrace, ProjectionError> {
    trace
        .iter()
        .enumerate()
        .map(|(index, event)| match event {
            BoundaryEvent::Clock { at } => Ok(BoundaryEvent::Clock { at: *at }),
            BoundaryEvent::Input {
                recipient: ConcretePid::Node(_),
                at,
                message: ConcreteMessage::Request(call),
            } => Ok(BoundaryEvent::Input {
                recipient: AbstractPid::Service,
                at: *at,
                message: AbstractMessage::Request(call.clone()),
            }),
            BoundaryEvent::Output {
                sender: ConcretePid::Node(_),
                at,
                message: ConcreteMessage::Output(output),
            } => Ok(BoundaryEvent::Output {
                sender: AbstractPid::Service,
                at: *at,
                message: AbstractMessage::Output(output.clone()),
            }),
            BoundaryEvent::Input { .. } => Err(ProjectionError {
                index,
                reason: "concrete input is not a client request to a node",
            }),
            BoundaryEvent::Output { .. } => Err(ProjectionError {
                index,
                reason: "concrete output is not a node protocol output",
            }),
        })
        .collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckOutcome {
    Certified { certificate: AbstractCertificate },
}

/// Scope of the executable concrete model used by this experiment.
///
/// The fleet is created once by `RoverConcreteSpec::processes`; the store
/// computes its normal in-memory outcomes.  In particular this driver does
/// not synthesize lifecycle events or fault responses that the concrete
/// model cannot produce.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Capabilities {
    pub fixed_nodes: u64,
    pub dynamic_membership: bool,
    pub crash_restart: bool,
    pub clean_stop: bool,
    pub join: bool,
    pub clock_skew_or_drift: bool,
    pub deterministic_store: bool,
    pub injected_unavailable: bool,
    pub injected_conflicts: bool,
    pub injected_lost_acks: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Options {
    pub seed: u64,
    pub nodes: u64,
    pub clients: usize,
    pub operations: usize,
    /// Maximum calls injected without an observed response.
    pub max_outstanding: usize,
    pub origins: u64,
    pub promises_per_origin: u64,
    pub schedules: bool,
    pub timeout_ms: u64,
    pub ttl_ms: u64,
    /// Largest seeded virtual-clock jump.
    pub max_clock_step: u64,
    pub loops: bool,
    pub appendable: bool,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            seed: 1,
            nodes: 3,
            clients: 4,
            operations: 12,
            max_outstanding: 4,
            origins: 6,
            promises_per_origin: 3,
            schedules: false,
            timeout_ms: 3_000,
            ttl_ms: 4_000,
            max_clock_step: 400,
            loops: true,
            appendable: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlowStats {
    pub requests: usize,
    pub request_kinds: BTreeMap<String, usize>,
    pub responses: usize,
    pub dispatches: usize,
    pub nodes_configured: u64,
    pub nodes_used: usize,
    pub logical_clients: usize,
    pub store_requests: usize,
    pub store_replies: usize,
    pub store_reads: usize,
    pub store_writes: usize,
    pub store_precondition_failures: usize,
    pub store_unavailable: usize,
    pub store_lost_acks: usize,
    pub internal_deliveries: usize,
    pub timeout_steps: usize,
    pub clock_advances: usize,
    pub clock_elapsed: u64,
    pub max_outstanding: usize,
    pub overlapping_pairs: usize,
    pub reordered_responses: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Report {
    pub seed: u64,
    pub capabilities: Capabilities,
    pub trace: ConcreteTrace,
    pub certificate: ConcreteCertificate,
    pub abstract_trace: AbstractTrace,
    pub check: CheckOutcome,
    pub responses: Vec<(u64, Response)>,
    pub flow: FlowStats,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunError {
    InvalidOptions(&'static str),
    Execution(ExecError),
    Projection(ProjectionError),
    Incomplete {
        expected_responses: usize,
        observed_responses: usize,
    },
    Uncertified,
}

type ConcreteAction = Action<ConcretePid, ConcreteMessage>;

struct ClientState {
    name: String,
    rng: Rng,
    seen: Seen,
    issued: usize,
    active: BTreeSet<u64>,
}

struct PendingCall {
    client: usize,
    recipient: ConcretePid,
    call: Call,
    injected: bool,
}

struct SeededStrategy {
    rng: Rng,
    generator: Generator,
    operations: usize,
    max_outstanding: usize,
    max_clock_step: u64,
    nodes: u64,
    clients: Vec<ClientState>,
    issued: usize,
    next_id: u64,
    calls: BTreeMap<u64, PendingCall>,
    generated_kinds: BTreeSet<String>,
    injection_order: Vec<u64>,
    delivered_requests: BTreeSet<u64>,
    active_nodes: BTreeMap<ConcretePid, u64>,
    delivered_store_requests: BTreeSet<(ConcretePid, u64)>,
    delivered_store_replies: BTreeSet<(ConcretePid, u64)>,
    delivered_timeouts: BTreeSet<(ConcretePid, u64)>,
    observed_responses: BTreeSet<u64>,
    observed_dispatches: BTreeSet<(ConcretePid, Output)>,
    clock_advances: usize,
}

impl SeededStrategy {
    fn new(options: &Options) -> Self {
        let mut client_rng = Rng::new(options.seed ^ 0xc11e_17);
        let clients = (0..options.clients)
            .map(|index| ClientState {
                name: format!("client{index}"),
                rng: client_rng.fork(),
                seen: Seen::default(),
                issued: 0,
                active: BTreeSet::new(),
            })
            .collect();
        Self {
            rng: Rng::new(options.seed ^ 0x57a7_e9a1),
            generator: Generator {
                origins: options.origins,
                promises_per_origin: options.promises_per_origin,
                schedules: options.schedules,
                timeout_ms: options.timeout_ms,
                ttl_ms: options.ttl_ms,
            },
            operations: options.operations,
            max_outstanding: options.max_outstanding,
            max_clock_step: options.max_clock_step,
            nodes: options.nodes,
            clients,
            issued: 0,
            next_id: 1,
            calls: BTreeMap::new(),
            generated_kinds: BTreeSet::new(),
            injection_order: Vec::new(),
            delivered_requests: BTreeSet::new(),
            active_nodes: BTreeMap::new(),
            delivered_store_requests: BTreeSet::new(),
            delivered_store_replies: BTreeSet::new(),
            delivered_timeouts: BTreeSet::new(),
            observed_responses: BTreeSet::new(),
            observed_dispatches: BTreeSet::new(),
            clock_advances: 0,
        }
    }

    fn pick(&mut self, choices: &[ConcreteAction]) -> Option<ConcreteAction> {
        if choices.is_empty() {
            None
        } else {
            let index = self.rng.below(choices.len() as u64) as usize;
            Some(choices[index].clone())
        }
    }

    fn outstanding(&self) -> usize {
        self.issued - self.observed_responses.len()
    }

    /// Draw from the shared workload generator, preferring a request family
    /// this run has not issued yet. Seen state is per logical client and is
    /// updated only from that client's concrete responses.
    fn generate_for(&mut self, client: usize, now: u64) -> Request {
        let mut fallback = None;
        for _ in 0..512 {
            let state = &mut self.clients[client];
            let request = self.generator.next(&mut state.rng, &state.seen, now);
            let kind = request_kind(&request).to_string();
            if fallback.is_none() {
                fallback = Some(request.clone());
            }
            if !self.generated_kinds.contains(&kind) {
                self.generated_kinds.insert(kind);
                return request;
            }
        }
        fallback.expect("workload generator always returns a request")
    }

    fn fill_window(&mut self, now: u64) {
        while self.issued < self.operations && self.outstanding() < self.max_outstanding {
            let least = self
                .clients
                .iter()
                .map(|client| client.issued)
                .min()
                .unwrap_or(0);
            let balanced: Vec<_> = self
                .clients
                .iter()
                .enumerate()
                .filter(|(_, client)| client.issued == least)
                .map(|(index, _)| index)
                .collect();
            let client = balanced[self.rng.below(balanced.len() as u64) as usize];
            let request = self.generate_for(client, now);
            let id = self.next_id;
            self.next_id += 1;
            self.issued += 1;
            self.clients[client].issued += 1;
            self.clients[client].active.insert(id);
            let call = Call {
                client: self.clients[client].name.clone(),
                id,
                request,
            };
            let recipient = route(&call.request, self.nodes);
            self.calls.insert(
                id,
                PendingCall {
                    client,
                    recipient,
                    call,
                    injected: false,
                },
            );
        }
    }

    fn first_waiting_for(&self, process: ConcretePid) -> Option<u64> {
        self.injection_order.iter().copied().find(|id| {
            !self.delivered_requests.contains(id)
                && self
                    .calls
                    .get(id)
                    .is_some_and(|pending| pending.recipient == process)
        })
    }

    fn record(&mut self, action: &ConcreteAction) {
        match action {
            Action::Inject {
                message: ConcreteMessage::Request(call),
                ..
            } => {
                if let Some(pending) = self.calls.get_mut(&call.id) {
                    pending.injected = true;
                    self.injection_order.push(call.id);
                }
            }
            Action::Process {
                process,
                at,
                event:
                    ProcessEvent::Receive {
                        sender: ConcretePid::Outside,
                        message: ConcreteMessage::Request(call),
                    },
                ..
            } => {
                self.delivered_requests.insert(call.id);
                self.active_nodes.insert(*process, call.id);
                self.delivered_timeouts.remove(&(*process, *at));
            }
            Action::Process {
                event:
                    ProcessEvent::Receive {
                        sender,
                        message: ConcreteMessage::StoreReq { op, .. },
                    },
                ..
            } => {
                self.delivered_store_requests.insert((*sender, *op));
            }
            Action::Process {
                process,
                event:
                    ProcessEvent::Receive {
                        sender: ConcretePid::Store,
                        message: ConcreteMessage::StoreReply { op, .. },
                    },
                ..
            } => {
                self.delivered_store_replies.insert((*process, *op));
            }
            Action::Process {
                process,
                at,
                event: ProcessEvent::Timeout,
                ..
            } => {
                self.delivered_timeouts.insert((*process, *at));
            }
            Action::Observe {
                message: ConcreteMessage::Output(Output::Response { id, response, .. }),
                ..
            } => {
                if self.observed_responses.insert(*id) {
                    if let Some(pending) = self.calls.get(id) {
                        self.active_nodes.remove(&pending.recipient);
                        let client = &mut self.clients[pending.client];
                        client.active.remove(id);
                        client.seen.note(response);
                    }
                }
            }
            Action::Observe {
                sender,
                message: ConcreteMessage::Output(output @ Output::Dispatch(_)),
                ..
            } => {
                self.observed_dispatches.insert((*sender, output.clone()));
            }
            Action::Clock { .. } => self.clock_advances += 1,
            _ => {}
        }
    }
}

impl Strategy<RoverConcreteExecAdapter> for SeededStrategy {
    fn next(&mut self, driver: Driver<'_, RoverConcreteExecAdapter>) -> Option<ConcreteAction> {
        self.fill_window(driver.now);
        if self.issued == self.operations && self.outstanding() == 0 {
            if self.clock_advances == 0 {
                let selected = Action::Clock {
                    at: driver.now + self.rng.range(1, self.max_clock_step),
                };
                self.record(&selected);
                return Some(selected);
            }
            return None;
        }

        // Expose a genuinely concurrent boundary before doing hidden work.
        let injections: Vec<_> = self
            .calls
            .values()
            .filter(|pending| !pending.injected)
            .map(|pending| Action::Inject {
                recipient: pending.recipient,
                at: driver.now,
                message: ConcreteMessage::Request(pending.call.clone()),
            })
            .collect();
        if let Some(selected) = self.pick(&injections) {
            self.record(&selected);
            return Some(selected);
        }

        let mut choices = Vec::new();
        choices.extend(
            driver
                .internal
                .iter()
                .filter(|action| {
                    matches!(
                        action,
                        Action::Process {
                            process,
                            event: ProcessEvent::Receive {
                                sender: ConcretePid::Outside,
                                message: ConcreteMessage::Request(call),
                            },
                            ..
                        } if !self.active_nodes.contains_key(process)
                            && self.first_waiting_for(*process) == Some(call.id)
                    )
                })
                .cloned(),
        );
        choices.extend(
            driver
                .internal
                .iter()
                .filter(|action| {
                    matches!(
                        action,
                        Action::Process {
                            event: ProcessEvent::Receive {
                                sender,
                                message: ConcreteMessage::StoreReq { op, .. },
                            },
                            ..
                        } if !self.delivered_store_requests.contains(&(*sender, *op))
                    )
                })
                .cloned(),
        );
        choices.extend(
            driver
                .internal
                .iter()
                .filter(|action| {
                    matches!(
                        action,
                        Action::Process {
                            process,
                            event: ProcessEvent::Receive {
                                sender: ConcretePid::Store,
                                message: ConcreteMessage::StoreReply { op, .. },
                            },
                            ..
                        } if !self.delivered_store_replies.contains(&(*process, *op))
                    )
                })
                .cloned(),
        );
        choices.extend(
            driver
                .internal
                .iter()
                .filter(|action| {
                    matches!(
                        action,
                        Action::Process {
                            process,
                            at,
                            event: ProcessEvent::Timeout,
                            ..
                        } if !self.active_nodes.contains_key(process)
                            && !self.delivered_timeouts.contains(&(*process, *at))
                    )
                })
                .cloned(),
        );
        choices.extend(
            driver
                .observe
                .iter()
                .filter(|action| {
                    matches!(
                        action,
                        Action::Observe {
                            message: ConcreteMessage::Output(Output::Response { id, .. }),
                            ..
                        } if !self.observed_responses.contains(id)
                    )
                })
                .cloned(),
        );
        choices.extend(
            driver
                .observe
                .iter()
                .filter(|action| {
                    matches!(
                        action,
                        Action::Observe {
                            sender,
                            message: ConcreteMessage::Output(output @ Output::Dispatch(_)),
                            ..
                        } if !self.observed_dispatches.contains(&(*sender, output.clone()))
                    )
                })
                .cloned(),
        );

        let clock_limit = self.operations.max(2) / 2 + 1;
        let waiting_for_delivery = self
            .injection_order
            .iter()
            .any(|id| !self.delivered_requests.contains(id));
        if !waiting_for_delivery
            && self.clock_advances < clock_limit
            && (choices.is_empty() || self.rng.percent(20))
        {
            choices.push(Action::Clock {
                at: driver.now + self.rng.range(1, self.max_clock_step),
            });
        }

        let selected = self.pick(&choices)?;
        self.record(&selected);
        Some(selected)
    }
}

fn document_key(request: &Request) -> String {
    let target = target_of(request);
    match target.strip_prefix("sched:") {
        Some(schedule) => format!("s/{schedule}"),
        None => format!("o/{target}"),
    }
}

fn route(request: &Request, nodes: u64) -> ConcretePid {
    ConcretePid::Node(echod_logic::keys::fnv1a(&document_key(request)) % nodes)
}

fn request_kind(request: &Request) -> &'static str {
    match request {
        Request::PromiseGet(_) => "promise.get",
        Request::PromiseCreate(_) => "promise.create",
        Request::PromiseSettle(_) => "promise.settle",
        Request::PromiseRegisterCallback(_) => "promise.register_callback",
        Request::PromiseRegisterListener(_) => "promise.register_listener",
        Request::ScheduleGet(_) => "schedule.get",
        Request::ScheduleCreate(_) => "schedule.create",
        Request::ScheduleDelete(_) => "schedule.delete",
        Request::TaskGet(_) => "task.get",
        Request::TaskCreate(_) => "task.create",
        Request::TaskAcquire(_) => "task.acquire",
        Request::TaskFulfill(_) => "task.fulfill",
        Request::TaskRelease(_) => "task.release",
        Request::TaskHalt(_) => "task.halt",
        Request::TaskContinue(_) => "task.continue",
        Request::TaskFence(_) | Request::TaskFenceCheck(_) => "task.fence",
        Request::TaskHeartbeat(_) => "task.heartbeat",
        Request::TaskSuspend(_) => "task.suspend",
    }
}

fn is_store_read(call: &StoreCall) -> bool {
    matches!(
        call,
        StoreCall::Get { .. }
            | StoreCall::GetIfNoneMatch { .. }
            | StoreCall::List { .. }
            | StoreCall::ListPrefixes { .. }
    )
}

fn is_store_write(call: &StoreCall) -> bool {
    !is_store_read(call)
}

fn responses(trace: &[BoundaryEvent<ConcretePid, ConcreteMessage>]) -> Vec<(u64, Response)> {
    trace
        .iter()
        .filter_map(|event| match event {
            BoundaryEvent::Output {
                message: ConcreteMessage::Output(Output::Response { id, response, .. }),
                ..
            } => Some((*id, response.clone())),
            _ => None,
        })
        .collect()
}

fn flow(certificate: &[ConcreteAction], options: &Options) -> FlowStats {
    let mut stats = FlowStats {
        requests: 0,
        request_kinds: BTreeMap::new(),
        responses: 0,
        dispatches: 0,
        nodes_configured: options.nodes,
        nodes_used: 0,
        logical_clients: options.clients,
        store_requests: 0,
        store_replies: 0,
        store_reads: 0,
        store_writes: 0,
        store_precondition_failures: 0,
        store_unavailable: 0,
        store_lost_acks: 0,
        internal_deliveries: 0,
        timeout_steps: 0,
        clock_advances: 0,
        clock_elapsed: 0,
        max_outstanding: 0,
        overlapping_pairs: 0,
        reordered_responses: 0,
    };
    let mut nodes = BTreeSet::new();
    let mut intervals = BTreeMap::<u64, (usize, usize)>::new();
    let mut starts = BTreeMap::<u64, usize>::new();
    let mut outstanding = 0usize;
    let mut now = 0u64;

    for (step, action) in certificate.iter().enumerate() {
        match action {
            Action::Inject {
                recipient,
                message: ConcreteMessage::Request(call),
                ..
            } => {
                stats.requests += 1;
                *stats
                    .request_kinds
                    .entry(request_kind(&call.request).to_string())
                    .or_default() += 1;
                nodes.insert(*recipient);
                starts.insert(call.id, step);
                outstanding += 1;
                stats.max_outstanding = stats.max_outstanding.max(outstanding);
            }
            Action::Observe {
                message: ConcreteMessage::Output(Output::Response { id, .. }),
                ..
            } => {
                stats.responses += 1;
                outstanding = outstanding.saturating_sub(1);
                if let Some(start) = starts.get(id) {
                    intervals.insert(*id, (*start, step));
                }
            }
            Action::Observe {
                message: ConcreteMessage::Output(Output::Dispatch(_)),
                ..
            } => stats.dispatches += 1,
            Action::Process {
                event: ProcessEvent::Receive { message, .. },
                ..
            } => {
                stats.internal_deliveries += 1;
                match message {
                    ConcreteMessage::StoreReq { call, .. } => {
                        stats.store_requests += 1;
                        stats.store_reads += usize::from(is_store_read(call));
                        stats.store_writes += usize::from(is_store_write(call));
                    }
                    ConcreteMessage::StoreReply { outcome, .. } => {
                        stats.store_replies += 1;
                        match outcome {
                            StoreOutcome::Failed(StoreError::PreconditionFailed) => {
                                stats.store_precondition_failures += 1
                            }
                            StoreOutcome::Failed(StoreError::Unavailable(_)) => {
                                stats.store_unavailable += 1
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            }
            Action::Process {
                event: ProcessEvent::Timeout,
                ..
            } => stats.timeout_steps += 1,
            Action::Clock { at } => {
                stats.clock_advances += 1;
                stats.clock_elapsed += at.saturating_sub(now);
                now = *at;
            }
            _ => {}
        }
    }
    stats.nodes_used = nodes.len();

    let intervals: Vec<_> = intervals.values().copied().collect();
    for (index, (a_start, a_end)) in intervals.iter().enumerate() {
        for (b_start, b_end) in &intervals[index + 1..] {
            if a_start < b_end && b_start < a_end {
                stats.overlapping_pairs += 1;
            }
            if (a_start < b_start && b_end < a_end) || (b_start < a_start && a_end < b_end) {
                stats.reordered_responses += 1;
            }
        }
    }
    stats
}

fn fleet(options: &Options) -> Fleet {
    Fleet {
        nodes: options.nodes,
        loops: options.loops,
        appendable: options.appendable,
        retry_timeout: RETRY_TIMEOUT,
    }
}

fn validate(options: &Options) -> Result<(), RunError> {
    if options.nodes == 0 {
        return Err(RunError::InvalidOptions("nodes must be positive"));
    }
    if options.clients == 0 {
        return Err(RunError::InvalidOptions("clients must be positive"));
    }
    if options.max_outstanding == 0 {
        return Err(RunError::InvalidOptions("max_outstanding must be positive"));
    }
    if options.origins == 0 {
        return Err(RunError::InvalidOptions("origins must be positive"));
    }
    if options.promises_per_origin == 0 {
        return Err(RunError::InvalidOptions(
            "promises_per_origin must be positive",
        ));
    }
    if options.max_clock_step == 0 {
        return Err(RunError::InvalidOptions("max_clock_step must be positive"));
    }
    Ok(())
}

/// Execute and certify a configurable deterministic production-backed run.
pub fn run_with_options(options: Options) -> Result<Report, RunError> {
    validate(&options)?;
    let expected_responses = options.operations;
    let config = fleet(&options);
    let max_steps = options.operations.saturating_mul(24).saturating_add(64);
    let execution = exec(
        &RoverConcreteExecAdapter,
        &config,
        max_steps,
        SeededStrategy::new(&options),
    )
    .map_err(RunError::Execution)?;
    let observed = responses(&execution.trace);
    if observed.len() != expected_responses {
        return Err(RunError::Incomplete {
            expected_responses,
            observed_responses: observed.len(),
        });
    }

    let abstract_trace = project(&execution.trace).map_err(RunError::Projection)?;
    let expected = abstract_trace
        .iter()
        .filter_map(|event| match event {
            BoundaryEvent::Output {
                message: AbstractMessage::Output(Output::Response { id, response, .. }),
                ..
            } => Some((*id, response.clone())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let limits = CheckConfig {
        max_steps: abstract_trace.len().saturating_mul(8).saturating_add(48),
        max_nodes: 50_000,
    };
    let abstract_certificate = check(
        &RoverAbstractExec,
        &ServerConfig {
            retry_timeout: RETRY_TIMEOUT,
        },
        &abstract_trace,
        limits,
        |event, action, sent| history_rank(event, action, sent, &expected),
    );
    let Some(abstract_certificate) = abstract_certificate else {
        if std::env::var_os("ROVER_DEBUG").is_some() {
            for (index, event) in abstract_trace.iter().enumerate() {
                eprintln!("{index}: {event:?}");
            }
        }
        return Err(RunError::Uncertified);
    };
    let stats = flow(&execution.certificate, &options);

    Ok(Report {
        seed: options.seed,
        capabilities: Capabilities {
            fixed_nodes: options.nodes,
            dynamic_membership: false,
            crash_restart: false,
            clean_stop: false,
            join: false,
            clock_skew_or_drift: false,
            deterministic_store: true,
            injected_unavailable: false,
            injected_conflicts: false,
            injected_lost_acks: false,
        },
        trace: execution.trace,
        certificate: execution.certificate,
        abstract_trace,
        check: CheckOutcome::Certified {
            certificate: abstract_certificate,
        },
        responses: observed,
        flow: stats,
    })
}

/// Execute and certify the default experiment for `seed`.
pub fn run(seed: u64) -> Result<Report, RunError> {
    run_with_options(Options {
        seed,
        ..Options::default()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use echod_logic::concrete::StoreCall;

    fn focused(seed: u64, schedules: bool, operations: usize) -> Options {
        Options {
            seed,
            nodes: 3,
            clients: 4,
            operations,
            max_outstanding: 4,
            origins: 8,
            schedules,
            max_clock_step: if schedules { 1_200 } else { 300 },
            ..Options::default()
        }
    }

    #[test]
    fn multiple_nodes_clients_and_request_families_are_certified() {
        let report = run_with_options(focused(0x5eed, false, 10))
            .unwrap_or_else(|error| panic!("focused seed: {error:?}"));
        assert_eq!(report.flow.requests, 10);
        assert_eq!(report.flow.responses, 10);
        assert_eq!(report.flow.nodes_used, 3);
        assert_eq!(report.flow.logical_clients, 4);
        assert!(report.flow.max_outstanding >= 4);
        assert!(report.flow.overlapping_pairs > 0);
        assert!(report.flow.reordered_responses > 0);
        assert!(report.flow.request_kinds.len() >= 9);
        assert!(report.flow.store_requests > 0);
        assert_eq!(report.flow.store_requests, report.flow.store_replies);
        assert!(report.flow.clock_advances > 0);
        assert_eq!(report.flow.store_unavailable, 0);
        assert_eq!(report.flow.store_lost_acks, 0);
        assert!(!report.capabilities.dynamic_membership);
        assert!(report.capabilities.deterministic_store);
        let CheckOutcome::Certified { certificate } = &report.check;
        assert!(!certificate.is_empty());
    }

    #[test]
    fn optional_schedule_family_is_exercised_and_certified() {
        let report = run_with_options(focused(73, true, 18))
            .unwrap_or_else(|error| panic!("schedule seed: {error:?}"));
        assert_eq!(report.flow.request_kinds.len(), 18);
        assert!(report.flow.request_kinds.contains_key("schedule.create"));
        assert!(report.flow.request_kinds.contains_key("schedule.get"));
        assert!(report.flow.request_kinds.contains_key("schedule.delete"));
        assert!(report.flow.nodes_used > 1);
        assert!(report.flow.max_outstanding > 1);
        assert!(report.flow.clock_elapsed > 0);
    }

    #[test]
    fn a_seed_replays_exactly() {
        let options = focused(42, false, 7);
        let first = run_with_options(options.clone()).expect("first certified run");
        let replayed = run_with_options(options.clone()).expect("replayed certified run");
        assert_eq!(first, replayed);
        assert_eq!(
            echod_rover_exec::replay(
                &RoverConcreteExecAdapter,
                &fleet(&options),
                &first.trace,
                &first.certificate,
            ),
            Ok(())
        );
    }

    #[test]
    fn projection_rejects_store_traffic_at_the_boundary() {
        let trace = vec![BoundaryEvent::Output {
            sender: ConcretePid::Store,
            at: 3,
            message: ConcreteMessage::StoreReq {
                op: 1,
                call: StoreCall::Get { key: "k".into() },
            },
        }];
        assert_eq!(
            project(&trace),
            Err(ProjectionError {
                index: 0,
                reason: "concrete output is not a node protocol output",
            })
        );
    }
}
