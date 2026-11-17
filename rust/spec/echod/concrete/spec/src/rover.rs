//! rover definitions for the concrete model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::state::{Message, LogicV, Proc, NodeV, StoreReq, StoreRes, StoreV};
#[cfg(verus_keep_ghost)]
use crate::handler::{on_event};
use rover_spec::rover::comm::Time;

verus! {
pub struct ProductionFleetSpec;
pub struct ProductionPublicSpec;

impl RoverSpec::Spec for ProductionPublicSpec {
    type Config = crate::state::ProductionFleetConfig;
    type Pid = Pid;
    type Proc = crate::state::ProductionFleetModel;
    type Message = crate::state::ProductionWireMessage;
    type Boundary = Result<echod_types::protocol::TimedBoundaryEvent, rover_spec::rover::comm::BoundaryEvent<Pid, Self::Message>>;
    open spec fn outside(&self) -> Pid { Pid::Outside }
    open spec fn processes(&self, config: Self::Config) -> Seq<(Pid, Self::Proc)> {
        ProductionFleetSpec.processes(config)
    }
    open spec fn injectable(&self, _config: Self::Config, message: Self::Message) -> bool {
        message is PublicRequest
    }
    open spec fn observe(&self, label: Label<Pid, Self::Message>) -> Seq<Self::Boundary> {
        crate::handler::production_protocol_observe(label)
    }
}

impl RoverSpec::Proc for crate::state::ProductionFleetModel {
    type Config = crate::state::ProductionFleetConfig;
    type Pid = Pid;
    type Message = crate::state::ProductionWireMessage;

    open spec fn on_event(self, config: Self::Config, now: Time, event: ProcessEvent<Pid, Self::Message>)
        -> Seq<StepResultV<Self, Pid, Self::Message>> {
        crate::handler::production_fleet_step(self, config, now, event)
    }
}

pub open spec fn production_initial_fleet_node(
    config: crate::state::ProductionConfigData, loops: bool, id: u64,
) -> crate::state::ProductionFleetModel {
    crate::state::ProductionFleetModel::Node(crate::state::ProductionRoutedNodeV {
        node: crate::state::ProductionNodeModel {
            core: crate::state::ProductionStateV { loops, ..crate::handler::production_state_spec_state_new(config.deep_view()) },
        },
        id, wake: Some((0, echod_types::ProductionArmed::Heartbeat)), next_request: 1, pending: Seq::empty(),
    })
}

impl RoverSpec::Spec for ProductionFleetSpec {
    type Config = crate::state::ProductionFleetConfig;
    type Pid = Pid;
    type Proc = crate::state::ProductionFleetModel;
    type Message = crate::state::ProductionWireMessage;
    type Boundary = rover_spec::rover::comm::BoundaryEvent<Pid, Self::Message>;

    open spec fn outside(&self) -> Pid { Pid::Outside }

    open spec fn processes(&self, config: Self::Config) -> Seq<(Pid, Self::Proc)> {
        config.nodes@.map(|i: int, node: crate::state::ProductionConfigData|
            (Pid::Node(i as u64), production_initial_fleet_node(node, config.loops, i as u64)))
        + seq![(Pid::Store, crate::state::ProductionFleetModel::Store(StoreV {
            entries: Seq::empty(), appendable: config.appendable, seen: Seq::empty(),
        }))]
    }

    open spec fn injectable(&self, _config: Self::Config, message: Self::Message) -> bool {
        match message {
            crate::state::ProductionWireMessage::PublicRequest(_) => true,
            crate::state::ProductionWireMessage::Input(crate::state::ProductionInput::Request { .. }) |
            crate::state::ProductionWireMessage::Input(crate::state::ProductionInput::Debug { .. }) => true,
            _ => false,
        }
    }

    open spec fn observe(&self, label: Label<Pid, Self::Message>) -> Seq<Self::Boundary> {
        match label {
            Label::Input { recipient, at, message } => seq![Self::Boundary::Input { recipient, at, message }],
            Label::Outside { sender, at, message } => seq![Self::Boundary::Output { sender, at, message }],
            _ => Seq::empty(),
        }
    }
}

pub struct ProductionNodeSpec;

impl RoverSpec::Proc for crate::state::ProductionNodeModel {
    type Config = crate::state::ProductionModelConfig;
    type Pid = Pid;
    type Message = crate::state::ProductionWireMessage;

    open spec fn on_event(self, _config: Self::Config, _now: Time, event: ProcessEvent<Pid, Self::Message>)
        -> Seq<StepResultV<Self, Pid, Self::Message>> {
        crate::handler::production_node_step(self, event)
    }
}

impl RoverSpec::Spec for ProductionNodeSpec {
    type Config = crate::state::ProductionModelConfig;
    type Pid = Pid;
    type Proc = crate::state::ProductionNodeModel;
    type Message = crate::state::ProductionWireMessage;
    type Boundary = rover_spec::rover::comm::BoundaryEvent<Pid, Self::Message>;

    open spec fn outside(&self) -> Pid { Pid::Outside }

    open spec fn processes(&self, config: Self::Config) -> Seq<(Pid, Self::Proc)> {
        seq![(Pid::Node(0), crate::state::ProductionNodeModel {
            core: crate::state::ProductionStateV {
                loops: config.loops,
                ..crate::handler::production_state_spec_state_new(config.node.deep_view())
            },
        })]
    }

    open spec fn injectable(&self, _config: Self::Config, message: Self::Message) -> bool {
        message is Input
    }

    open spec fn observe(&self, label: Label<Pid, Self::Message>) -> Seq<Self::Boundary> {
        match label {
            Label::Input { recipient, at, message } => seq![Self::Boundary::Input { recipient, at, message }],
            Label::Outside { sender, at, message } => seq![Self::Boundary::Output { sender, at, message }],
            _ => Seq::empty(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Pid {
    Outside,
    Node(u64),
    Store,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    /// Node ids are `0 .. nodes`.
    pub nodes: u64,
    /// Whether each node keeps its heartbeat and timers after it starts.
    pub loops: bool,
    /// Whether the store accepts an append.
    pub appendable: bool,
    /// How long a pending task waits before it is offered again. The
    /// abstract model's `Config.retry_timeout`, Lean's `retryTimeout`.
    pub retry_timeout: u64,
}

pub struct Spec;

impl RoverSpec::Proc for Proc {
    type Config = Config;
    type Pid = Pid;
    type Message = Message;

    open spec fn on_event(
        self,
        _config: Config,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<Proc, Pid, Message>> {
        crate::handler::on_event(self, now, event)
    }
}

pub open spec fn spec_nodes(config: Config, id: u64) -> Seq<(Pid, Proc)>
    decreases (config.nodes - id) as int
{
    if id >= config.nodes {
        Seq::empty()
    } else {
        seq![(Pid::Node(id), Proc::Node(spec_initial_node(config, id)))]
            + spec_nodes(config, (id + 1) as u64)
    }
}

pub open spec fn spec_initial_node(config: Config, id: u64) -> NodeV {
    NodeV {
        logic: LogicV {
            clock: 0,
            loops: config.loops,
            stopping: false,
            stopped: false,
            last_wake: None,
        },
        wake: None,
        next_request: 1,
        address: id as nat,
        nodes: config.nodes as nat,
        retry_timeout: config.retry_timeout,
        flight: None,
        documents: Seq::empty(),
        pending: Seq::empty(),
        next_op: 1,
    }
}

pub open spec fn spec_world(config: Config) -> Seq<(Pid, Proc)> {
    spec_nodes(config, 0) + seq![(
        Pid::Store,
        Proc::Store(StoreV {
            entries: Seq::empty(),
            appendable: config.appendable,
            seen: Seq::empty(),
        }),
    )]
}

pub const RETRY_TIMEOUT: u64 = 5_000;

impl Config {
    pub fn new(nodes: u64, loops: bool) -> Self {
        Self {
            nodes,
            loops,
            appendable: false,
            retry_timeout: RETRY_TIMEOUT,
        }
    }
}

impl RoverSpec::Spec for Spec {
    type Config = Config;
    type Pid = Pid;
    type Proc = Proc;
    type Message = Message;
    type Boundary = BoundaryEvent;

    open spec fn outside(&self) -> Pid {
        Pid::Outside
    }

    open spec fn processes(&self, config: Config) -> Seq<(Pid, Proc)> {
        spec_world(config)
    }

    open spec fn injectable(&self, _config: Config, message: Message) -> bool {
        match message {
            Message::Request(_) | Message::Stop => true,
            Message::Output(_) | Message::StoreReq { .. } | Message::StoreRes { .. } => false,
        }
    }

    /// A request in and an output out. Store traffic and `Stop` stay off the boundary,
    /// the same projection the abstract model uses for its own messages.
    open spec fn observe(&self, label: Label<Pid, Message>) -> Seq<BoundaryEvent> {
        match label {
            Label::Input { at, message: Message::Request(request), .. } => {
                seq![BoundaryEvent::Input { recipient: (), at, message: echod_types::Message::Request(request) }]
            }
            Label::Outside { at, message: Message::Output(output), .. } => {
                seq![BoundaryEvent::Output { sender: (), at, message: echod_types::Message::Output(output) }]
            }
            _ => Seq::empty(),
        }
    }
}
}
