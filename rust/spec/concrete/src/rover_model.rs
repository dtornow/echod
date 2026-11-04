//! The executable [`RoverModel`](echod_rover::rover::RoverModel).
//!
//! Rover assembles the world from [`Model::initial`]: the nodes and the
//! store, an empty network, time 0. A node step is `plane`. This file stays
//! out of a Verus run.

use echod_rover::rover::{ProcessEvent, RoverModel, StepResult};
use echod_rover::Time;

use crate::model::{Boundary, Fleet, Incoming, Local, LocalV, Message, Model, Pid};

impl RoverModel for Model {
    type Config = Fleet;
    type Pid = Pid;
    type StateV = LocalV;
    type State = Local;
    type Message = Message;
    type Boundary = Boundary;

    fn outside(&self) -> Pid {
        Pid::Outside
    }

    fn initial(&self, config: &Fleet) -> Vec<(Pid, Local)> {
        self.world(config).process
    }

    fn injectable(&self, _config: &Fleet, message: &Message) -> bool {
        matches!(message, Message::Request(_) | Message::Stop)
    }

    fn on_event(
        &self,
        _config: &Fleet,
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
