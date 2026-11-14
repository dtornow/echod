//! Domain payloads shared by the abstract and concrete Rover models.

use vstd::prelude::*;
use crate::{PromiseRecord, Request, Response};

verus! {

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Dispatch {
    Execute { id: String, version: u64 },
    Unblock { address: String, promise: PromiseRecord },
}

pub enum DispatchV {
    Execute { id: Seq<char>, version: u64 },
    Unblock { address: Seq<char>, promise: PromiseRecord },
}

impl View for Dispatch {
    type V = DispatchV;

    open spec fn view(&self) -> DispatchV {
        match self {
            Dispatch::Execute { id, version } => DispatchV::Execute { id: id@, version: *version },
            Dispatch::Unblock { address, promise } => DispatchV::Unblock { address: address@, promise: *promise },
        }
    }
}

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
    Response { client: String, id: u64, response: Response },
    Dispatch(Dispatch),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Request(Call),
    Output(Output),
}

/// Both models erase internal routing identities and emit only request inputs
/// and output messages; Rover's Clock variant is absent from their projections.
pub type BoundaryEvent = rover_spec::rover::comm::BoundaryEvent<(), Message>;

}
