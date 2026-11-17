//! rover definitions for the abstract model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::state::{Time, StoreV, Proc};
#[cfg(verus_keep_ghost)]
use crate::handler::{on_event};
#[cfg(verus_keep_ghost)]
use crate::axioms::*;

verus! {
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Config {
    pub retry_timeout: Time,
}

impl Default for Config {
    fn default() -> Self { Config { retry_timeout: 5_000 } }
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Pid {
    Outside,
    Service,
}

impl RoverSpec::Proc for Proc {
    type Config = Config;
    type Pid = Pid;
    type Message = Message;

    open spec fn on_event(
        self,
        config: Config,
        now: Time,
        event: ProcessEvent<Pid, Message>,
    ) -> Seq<StepResultV<Proc, Pid, Message>> {
        crate::handler::on_event(config, self, now, event)
    }
}

pub struct Spec;

pub open spec fn empty_store() -> StoreV {
    StoreV {
        promises: Map::empty(),
        tasks: Map::empty(),
        schedules: Map::empty(),
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

    open spec fn processes(&self, _config: Config) -> Seq<(Pid, Proc)> {
        seq![(
            Pid::Service,
            Proc {
                store: empty_store(),
                pending: Seq::empty(),
                detached: Seq::empty(),
            },
        )]
    }

    open spec fn injectable(&self, _config: Config, message: Message) -> bool {
        match message {
            Message::Request(_) => true,
            Message::Output(_) => false,
        }
    }

    open spec fn observe(
        &self,
        label: Label<Pid, Message>,
    ) -> Seq<BoundaryEvent> {
        match label {
            Label::Input {
                at,
                message: Message::Request(call),
                ..
            } => seq![BoundaryEvent::Input { recipient: (), at, message: Message::Request(call) }],
            Label::Outside {
                at,
                message: Message::Output(output),
                ..
            } => seq![BoundaryEvent::Output { sender: (), at, message: Message::Output(output) }],
            _ => Seq::empty(),
        }
    }
}
}
