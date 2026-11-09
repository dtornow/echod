//! Mathematical Rover processes, worlds, executions, and refinement.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use crate::{Data, Time};

use super::comm::{BoundaryEvent, Envelope, ProcessEvent};

pub mod refinement;
pub mod semantics;

verus! {

/// One stateful process in a Rover world.
///
/// A model-specific enum can implement this trait to present heterogeneous
/// process kinds as one homogeneous process type. The process value is its
/// complete local state; an outcome carries the next complete value.
pub trait RoverProc: Sized {
    type Config;
    type Pid: Data;
    type Message: Data;

    spec fn on_event(
        self,
        config: Self::Config,
        now: Time,
        event: ProcessEvent<Self::Pid, Self::Message>,
    ) -> Seq<semantics::StepResultV<Self, Self::Pid, Self::Message>>;
}

/// A complete mathematical Rover model.
///
/// World construction and stepping are generic over `Proc`; implementations
/// provide only initial processes, injection policy, and boundary projection.
pub trait RoverSpec: Sized {
    type Config;
    type Pid: Data;
    type Proc: RoverProc<Config = Self::Config, Pid = Self::Pid, Message = Self::Message>;
    type Message: Data;
    type Boundary;

    open spec fn spec_outside(&self) -> Self::Pid {
        arbitrary()
    }

    open spec fn spec_initial(&self, config: Self::Config) -> Seq<(Self::Pid, Self::Proc)> {
        arbitrary()
    }

    open spec fn spec_injectable(&self, config: Self::Config, message: Self::Message) -> bool {
        arbitrary()
    }

    open spec fn spec_observe(
        &self,
        label: semantics::Lab<Self>,
    ) -> Seq<Self::Boundary> {
        arbitrary()
    }

    open spec fn init(self, config: Self::Config) -> semantics::World<Self> {
        semantics::WorldV {
            process: self.spec_initial(config),
            network: Seq::empty(),
            now: 0,
        }
    }

    /// One complete world step: input, process delivery, or outside
    /// observation. Rover never inspects model-specific process variants.
    open spec fn step(
        self,
        config: Self::Config,
        before: semantics::World<Self>,
        label: semantics::Lab<Self>,
        after: semantics::World<Self>,
    ) -> bool {
        match label {
            semantics::Label::Input { recipient, at, message } => {
                &&& before.now <= at
                &&& recipient != self.spec_outside()
                &&& exists|i: int| 0 <= i < before.process.len()
                    && #[trigger] before.process[i].0 == recipient
                &&& self.spec_injectable(config, message)
                &&& after == semantics::inject(
                    before,
                    self.spec_outside(),
                    recipient,
                    at,
                    message,
                )
            }
            semantics::Label::Process { process, at, event, send } => {
                &&& before.now <= at
                &&& process != self.spec_outside()
                &&& semantics::event_valid(before, process, event)
                &&& exists|i: int, j: int|
                    #![trigger before.process[i].1.on_event(config, at, event)[j]]
                {
                    &&& 0 <= i < before.process.len()
                    &&& before.process[i].0 == process
                    &&& {
                        let outcomes = before.process[i].1.on_event(config, at, event);
                        &&& 0 <= j < outcomes.len()
                        &&& outcomes[j].send == send
                        &&& after == semantics::land(before, i, process, at, outcomes[j])
                    }
                }
            }
            semantics::Label::Outside { sender, at, message } => {
                &&& before.now <= at
                &&& exists|i: int| {
                    &&& 0 <= i < before.network.len()
                    &&& #[trigger] before.network[i] == Envelope {
                        sender,
                        recipient: self.spec_outside(),
                        message,
                    }
                }
                &&& after == semantics::observe_outside(before, at)
            }
        }
    }
}

} // verus!

pub type EventOf<M> =
    BoundaryEvent<<M as RoverSpec>::Pid, <M as RoverSpec>::Message>;
