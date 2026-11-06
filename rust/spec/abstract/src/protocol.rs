//! Process-independent boundary protocol shared by Rover Resonate models.

use vstd::prelude::*;

use echod_rover::Time;

use echod_types::{Request, Response};

use super::Dispatch;

verus! {

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Call {
    pub client: String,
    pub id: u64,
    pub request: Request,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Output {
    Response {
        client: String,
        id: u64,
        response: Response,
    },
    Dispatch(Dispatch),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Request(Call),
    Output(Output),
}

/// Clean PID-0 traffic. Internal process ids and messages are absent.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum BoundaryEvent {
    Input {
        at: Time,
        call: Call,
    },
    Output {
        at: Time,
        output: Output,
    },
}

} // verus!
