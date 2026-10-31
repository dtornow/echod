//! Process-independent boundary protocol shared by Rover Resonate models.

use vstd::prelude::*;

use crate::Time;

use super::{Dispatch, Request, Response};

verus! {

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Call {
    pub client: String,
    pub id: u64,
    pub requested_at: Time,
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

} // verus!
