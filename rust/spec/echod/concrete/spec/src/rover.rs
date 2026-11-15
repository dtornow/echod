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
