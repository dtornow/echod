//! The executable [`RoverModel`](echod_rover::rover::RoverModel).
//!
//! Rover assembles the world from [`Model::initial`]: the nodes, an empty
//! network, time 0. Each node keeps its own memory. The bucket is outside.
//! [`crate::model::spec_world`] is that
//! world as a specification, and [`crate::model::spec_step`] is its step.
//! This file stays out of the Verus run. The handler arms are still
//! uninterpreted, so the executable logic is the control in `State::on_event`
//! and not yet that whole specification.

use echod_rover::rover::{ProcessEvent, RoverModel, StepResult};
use echod_rover::Time;

use crate::model::{Boundary, Config, Incoming, Local, LocalV, Message, Model, Pid};

impl RoverModel for Model {
    type Config = Config;
    type Pid = Pid;
    type StateV = LocalV;
    type State = Local;
    type Message = Message;
    type Boundary = Boundary;

    fn outside(&self) -> Pid {
        Pid::Outside
    }

    fn initial(&self, config: &Config) -> Vec<(Pid, Local)> {
        self.world(config).process
    }

    fn injectable(&self, _config: &Config, message: &Message) -> bool {
        matches!(message, Message::Request(_) | Message::Stop)
    }

    fn on_event(
        &self,
        _config: &Config,
        pid: &Pid,
        state: &Local,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<StepResult<Self>> {
        let incoming = match event {
            ProcessEvent::Timeout => Incoming::Timeout,
            ProcessEvent::Receive { sender, message } => Incoming::Receive {
                sender: sender.clone(),
                message: message.clone(),
            },
        };
        self.step(pid, state, now, &incoming)
            .into_iter()
            .map(|transition| StepResult {
                state: transition.state,
                send: transition.send,
            })
            .collect()
    }
}
