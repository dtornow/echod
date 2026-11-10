//! Isolated executable-Rover experiment over the production concrete machine.
//!
//! This does not participate in the synchronous DST in [`crate::sim`].  It
//! supplies the small adapter that `echod-process` deliberately keeps behind
//! its own `cfg(test)`, drives [`echod_rover_exec::exec`], and projects the
//! concrete boundary onto the public abstract Rover boundary for checking.

use std::collections::{BTreeMap, BTreeSet};

use echod_logic::concrete::document::Node;
use echod_logic::concrete::model::{Fleet, Message as ConcreteMessage, Pid as ConcretePid};
use echod_logic::concrete::store::Store;
use echod_rover::rover::comm::{BoundaryEvent, ProcessEvent};
use echod_rover_exec::{
    check, exec, Action, Certificate, CheckConfig, Driver, ExecError, Proc, ProcResult, Spec,
    Strategy,
};
use echod_types::{
    PromiseCreateReq, PromiseGetReq, PromiseSettleReq, PromiseState, Request, Response, Value,
};
use rover_abstract_exec::{history_rank, RoverAbstractExec};
use rover_abstract_spec::model::Pid as AbstractPid;
use rover_abstract_spec::{Call, Message as AbstractMessage, Output, ServerConfig};
use rover_concrete_spec::model::{LocalV as ConcreteLocalV, RoverConcreteSpec, RETRY_TIMEOUT};
use vstd::prelude::View;

use crate::rng::Rng;

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlowStats {
    pub requests: usize,
    pub responses: usize,
    pub store_requests: usize,
    pub store_replies: usize,
    pub clock_advances: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Report {
    pub seed: u64,
    pub trace: ConcreteTrace,
    pub certificate: ConcreteCertificate,
    pub abstract_trace: AbstractTrace,
    pub check: CheckOutcome,
    pub responses: Vec<(u64, Response)>,
    pub flow: FlowStats,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunError {
    Execution(ExecError),
    Projection(ProjectionError),
    Incomplete {
        expected_responses: usize,
        observed_responses: usize,
    },
    Uncertified,
}

type ConcreteAction = Action<ConcretePid, ConcreteMessage>;

struct SeededStrategy {
    rng: Rng,
    calls: Vec<(u64, Call)>,
    current: usize,
    clocked: bool,
    injected: bool,
    request_delivered: bool,
    delivered_store_requests: BTreeSet<u64>,
    delivered_store_replies: BTreeSet<u64>,
}

impl SeededStrategy {
    fn new(seed: u64, calls: Vec<(u64, Call)>) -> Self {
        Self {
            rng: Rng::new(seed),
            calls,
            current: 0,
            clocked: false,
            injected: false,
            request_delivered: false,
            delivered_store_requests: BTreeSet::new(),
            delivered_store_replies: BTreeSet::new(),
        }
    }

    fn pick(&mut self, choices: Vec<ConcreteAction>) -> Option<ConcreteAction> {
        if choices.is_empty() {
            None
        } else {
            let index = self.rng.below(choices.len() as u64) as usize;
            Some(choices[index].clone())
        }
    }

    fn advance(&mut self) {
        self.current += 1;
        self.clocked = false;
        self.injected = false;
        self.request_delivered = false;
    }
}

impl Strategy<RoverConcreteExecAdapter> for SeededStrategy {
    fn next(&mut self, driver: Driver<'_, RoverConcreteExecAdapter>) -> Option<ConcreteAction> {
        let (at, call) = self.calls.get(self.current)?.clone();

        if !self.clocked {
            self.clocked = true;
            return Some(Action::Clock { at });
        }
        if !self.injected {
            self.injected = true;
            return Some(Action::Inject {
                recipient: ConcretePid::Node(0),
                at,
                message: ConcreteMessage::Request(call.clone()),
            });
        }
        if !self.request_delivered {
            let choices = driver
                .internal
                .iter()
                .filter(|action| {
                    matches!(
                        action,
                        Action::Process {
                            process: ConcretePid::Node(0),
                            event: ProcessEvent::Receive {
                                sender: ConcretePid::Outside,
                                message: ConcreteMessage::Request(candidate),
                            },
                            ..
                        } if candidate.id == call.id
                    )
                })
                .cloned()
                .collect();
            let selected = self.pick(choices)?;
            self.request_delivered = true;
            return Some(selected);
        }

        let responses = driver
            .observe
            .iter()
            .filter(|action| {
                matches!(
                    action,
                    Action::Observe {
                        message: ConcreteMessage::Output(Output::Response { id, .. }),
                        ..
                    } if *id == call.id
                )
            })
            .cloned()
            .collect();
        if let Some(response) = self.pick(responses) {
            self.advance();
            return Some(response);
        }

        let store_requests: Vec<_> = driver
            .internal
            .iter()
            .filter(|action| {
                matches!(
                    action,
                    Action::Process {
                        process: ConcretePid::Store,
                        event: ProcessEvent::Receive {
                            message: ConcreteMessage::StoreReq { op, .. },
                            ..
                        },
                        ..
                    } if !self.delivered_store_requests.contains(op)
                )
            })
            .cloned()
            .collect();
        if let Some(selected) = self.pick(store_requests) {
            if let Action::Process {
                event:
                    ProcessEvent::Receive {
                        message: ConcreteMessage::StoreReq { op, .. },
                        ..
                    },
                ..
            } = &selected
            {
                self.delivered_store_requests.insert(*op);
            }
            return Some(selected);
        }

        let store_replies: Vec<_> = driver
            .internal
            .iter()
            .filter(|action| {
                matches!(
                    action,
                    Action::Process {
                        process: ConcretePid::Node(0),
                        event: ProcessEvent::Receive {
                            sender: ConcretePid::Store,
                            message: ConcreteMessage::StoreReply { op, .. },
                        },
                        ..
                    } if !self.delivered_store_replies.contains(op)
                )
            })
            .cloned()
            .collect();
        let selected = self.pick(store_replies)?;
        if let Action::Process {
            event:
                ProcessEvent::Receive {
                    message: ConcreteMessage::StoreReply { op, .. },
                    ..
                },
            ..
        } = &selected
        {
            self.delivered_store_replies.insert(*op);
        }
        Some(selected)
    }
}

fn workload(seed: u64) -> Vec<(u64, Call)> {
    let mut rng = Rng::new(seed);
    let start = 10 + rng.below(20);
    let id = format!("sim{}:{:x}", rng.below(4), seed);
    let client = format!("seed-{seed}");
    let settled = if rng.percent(50) {
        PromiseState::Resolved
    } else {
        PromiseState::Rejected
    };
    let requests = [
        Request::PromiseCreate(PromiseCreateReq {
            id: id.clone(),
            timeout_at: start + 100,
            param: Value {
                headers: vec![("seed".into(), seed.to_string())],
                data: Some(format!("value-{seed}")),
            },
            tags: Vec::new(),
        }),
        Request::PromiseGet(PromiseGetReq { id: id.clone() }),
        Request::PromiseSettle(PromiseSettleReq {
            id: id.clone(),
            state: settled,
            value: Value {
                headers: Vec::new(),
                data: Some("settled".into()),
            },
        }),
        Request::PromiseGet(PromiseGetReq { id }),
    ];

    requests
        .into_iter()
        .enumerate()
        .map(|(index, request)| {
            (
                start + index as u64 * 3,
                Call {
                    client: client.clone(),
                    id: index as u64 + 1,
                    request,
                },
            )
        })
        .collect()
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

fn flow(certificate: &[ConcreteAction], response_count: usize) -> FlowStats {
    let mut stats = FlowStats {
        requests: 0,
        responses: response_count,
        store_requests: 0,
        store_replies: 0,
        clock_advances: 0,
    };
    for action in certificate {
        match action {
            Action::Inject {
                message: ConcreteMessage::Request(_),
                ..
            } => stats.requests += 1,
            Action::Process {
                event:
                    ProcessEvent::Receive {
                        message: ConcreteMessage::StoreReq { .. },
                        ..
                    },
                ..
            } => stats.store_requests += 1,
            Action::Process {
                event:
                    ProcessEvent::Receive {
                        message: ConcreteMessage::StoreReply { .. },
                        ..
                    },
                ..
            } => stats.store_replies += 1,
            Action::Clock { .. } => stats.clock_advances += 1,
            _ => {}
        }
    }
    stats
}

fn fleet() -> Fleet {
    Fleet {
        nodes: 1,
        loops: true,
        appendable: false,
        retry_timeout: RETRY_TIMEOUT,
    }
}

/// Execute and certify one deterministic production-backed experiment.
pub fn run(seed: u64) -> Result<Report, RunError> {
    let calls = workload(seed);
    let expected_responses = calls.len();
    let config = fleet();
    let execution = exec(
        &RoverConcreteExecAdapter,
        &config,
        64,
        SeededStrategy::new(seed, calls),
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
        max_steps: abstract_trace.len().saturating_mul(8).saturating_add(32),
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
    )
    .ok_or(RunError::Uncertified)?;
    let stats = flow(&execution.certificate, observed.len());

    Ok(Report {
        seed,
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

#[cfg(test)]
mod tests {
    use super::*;
    use echod_logic::concrete::StoreCall;

    #[test]
    fn several_seeds_run_through_store_and_are_abstractly_certified() {
        for seed in [1, 7, 0x5eed] {
            let report = run(seed).unwrap_or_else(|error| panic!("seed {seed}: {error:?}"));
            assert_eq!(report.flow.requests, 4);
            assert_eq!(report.flow.responses, 4);
            assert_eq!(report.flow.clock_advances, 4);
            assert!(report.flow.store_requests >= 2);
            assert_eq!(report.flow.store_requests, report.flow.store_replies);
            assert_eq!(report.trace.len(), report.abstract_trace.len());
            assert_eq!(report.trace.len(), 12);
            let CheckOutcome::Certified { certificate } = &report.check;
            assert!(!certificate.is_empty());
            assert!(certificate.len() <= 128);
        }
    }

    #[test]
    fn a_seed_replays_exactly() {
        let first = run(42).expect("first certified run");
        let replay = run(42).expect("replayed certified run");
        assert_eq!(first, replay);
        assert_eq!(
            echod_rover_exec::replay(
                &RoverConcreteExecAdapter,
                &fleet(),
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
