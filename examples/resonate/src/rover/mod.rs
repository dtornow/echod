//! Resonate's process-independent Rover protocol.
//!
//! This mirrors `rover/Resonate.lean`: calls enter the modeled world, while
//! responses and server-initiated dispatches leave it. The abstract and
//! concrete Rover models share these types.

use accordant::Time;
use vstd::prelude::*;

use crate::{Dispatch, Request, Response};

pub mod abstract_model;

verus! {

/// A complete client call. `requested_at` is protocol data and remains stable
/// if the request is delivered or processed later.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Call {
    pub client: String,
    pub id: u64,
    pub requested_at: Time,
    pub request: Request,
}

/// Values emitted across the modeled system boundary.
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

/// Messages carried by Rover's append-only network.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Request(Call),
    Output(Output),
}

/// Process-independent observations used by every Resonate Rover model.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum BoundaryEvent {
    Request {
        at: Time,
        call: Call,
    },
    Response {
        at: Time,
        client: String,
        id: u64,
        response: Response,
    },
    Dispatch {
        at: Time,
        dispatch: crate::Dispatch,
    },
}

} // verus!
