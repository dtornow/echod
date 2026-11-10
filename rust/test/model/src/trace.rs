//! History traces and Rover ranking support.

use std::collections::BTreeMap;
use echod_abstract_spec::rover::Pid;
use echod_abstract_spec::protocol::{Call, Dispatch, Message, Output};
use echod_types::{Request, Response};
use rover_exec::Action as ExecAction;
use rover_spec::rover::comm::{BoundaryEvent as RoverBoundaryEvent, ProcessEvent, Time};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HistoryEvent {
    Invoke { call: u64, req: Request },
    Return { call: u64, res: Response },
    Receive { msg: Dispatch },
    Clock { at: Time },
}


pub fn rover_trace(history: &[HistoryEvent]) -> Vec<RoverBoundaryEvent<Pid, Message>> {
    let mut now = 0;
    let mut trace = Vec::with_capacity(history.len());
    for event in history {
        match event {
            HistoryEvent::Clock { at } => {
                now = *at;
                trace.push(RoverBoundaryEvent::Clock { at: *at });
            }
            HistoryEvent::Invoke { call, req } => {
                trace.push(RoverBoundaryEvent::Input {
                    recipient: Pid::Service,
                    at: now,
                    message: Message::Request(Call {
                        client: "history".into(),
                        id: *call,
                        request: req.clone(),
                    }),
                });
            }
            HistoryEvent::Return { call, res } => {
                trace.push(RoverBoundaryEvent::Output {
                    sender: Pid::Service,
                    at: now,
                    message: Message::Output(Output::Response {
                        client: "history".into(),
                        id: *call,
                        response: res.clone(),
                    }),
                });
            }
            HistoryEvent::Receive { msg } => {
                trace.push(RoverBoundaryEvent::Output {
                    sender: Pid::Service,
                    at: now,
                    message: Message::Output(Output::Dispatch(msg.clone())),
                });
            }
        }
    }
    trace
}

pub fn history_rank(
    target: &RoverBoundaryEvent<Pid, Message>,
    action: &ExecAction<Pid, Message>,
    sent: &[rover_spec::rover::comm::Envelope<Pid, Message>],
    expected: &BTreeMap<u64, Response>,
) -> usize {
    match (target, action) {
        (
            RoverBoundaryEvent::Input {
                message: Message::Request(target),
                ..
            },
            ExecAction::Process {
                event: ProcessEvent::Receive {
                    message: Message::Request(call),
                    ..
                },
                ..
            },
        ) if call.id == target.id => {
            let response = sent.iter().find_map(|envelope| match &envelope.message {
                Message::Output(Output::Response { id, response, .. })
                    if *id == target.id =>
                {
                    Some(response)
                }
                _ => None,
            });
            match (expected.get(&target.id), response) {
                (Some(want), Some(have)) if want == have => 0,
                (_, Some(_)) => 1,
                _ => 2,
            }
        }
        (
            RoverBoundaryEvent::Output {
                message: Message::Output(Output::Response { id, .. }),
                ..
            },
            ExecAction::Process {
                event: ProcessEvent::Receive {
                    message: Message::Request(call),
                    ..
                },
                ..
            },
        ) if call.id == *id => 0,
        (
            RoverBoundaryEvent::Output {
                message: Message::Output(Output::Dispatch(_)),
                ..
            },
            ExecAction::Process {
                event: ProcessEvent::Receive { .. },
                ..
            },
        ) => 0,
        (_, ExecAction::Process { event: ProcessEvent::Receive { .. }, .. }) => 1,
        (_, ExecAction::Process { event: ProcessEvent::Timeout, .. }) => 2,
        _ => 3,
    }
}

pub fn history_responses(history: &[HistoryEvent]) -> BTreeMap<u64, Response> {
    history
        .iter()
        .filter_map(|event| match event {
            HistoryEvent::Return { call, res } => Some((*call, res.clone())),
            _ => None,
        })
        .collect()
}

