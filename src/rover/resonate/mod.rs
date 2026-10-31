//! A standalone Resonate promise model for Rover.
//!
//! This module owns its protocol and state. It does not depend on Accordant's
//! older Resonate model. `abstract_model` supplies the one-process Rover model.

use vstd::prelude::*;

use crate::Time;

pub mod abstract_model;

verus! {

pub type ClientId = u64;
pub type CallId = u64;
pub type PromiseId = u64;
pub type Address = u8;
pub type Value = i64;

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum PromiseState {
    Pending,
    Resolved,
    Rejected,
    Canceled,
    TimedOut,
}

impl PromiseState {
    pub open spec fn spec_settable(self) -> bool {
        self != PromiseState::Pending && self != PromiseState::TimedOut
    }

    pub fn settable(self) -> (settable: bool)
        ensures
            settable == self.spec_settable(),
    {
        self != PromiseState::Pending && self != PromiseState::TimedOut
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Debug)]
pub struct Promise {
    pub id: PromiseId,
    pub state: PromiseState,
    pub value: Value,
    pub timeout_at: Time,
    pub listener: Option<Address>,
}

#[derive(PartialEq, Eq, Debug)]
pub enum Promises {
    Nil,
    Cons(Promise, Box<Promises>),
}

#[derive(PartialEq, Eq, Debug)]
pub struct State {
    pub promises: Promises,
}

impl View for State {
    type V = State;

    open spec fn view(&self) -> State {
        *self
    }
}

impl Default for State {
    fn default() -> Self {
        Self {
            promises: Promises::Nil,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub struct Config {
    pub default_timeout: Time,
    pub unreliable: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            default_timeout: 1_000,
            unreliable: false,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Request {
    Get {
        id: PromiseId,
    },
    Create {
        id: PromiseId,
        timeout_at: Option<Time>,
    },
    Settle {
        id: PromiseId,
        state: PromiseState,
        value: Value,
    },
    Listen {
        id: PromiseId,
        address: Address,
    },
}

impl Request {
    pub open spec fn spec_key(self) -> PromiseId {
        match self {
            Request::Get { id }
            | Request::Create { id, .. }
            | Request::Settle { id, .. }
            | Request::Listen { id, .. } => id,
        }
    }

    pub fn key(&self) -> (id: PromiseId)
        ensures
            id == self.spec_key(),
    {
        match self {
            Request::Get { id }
            | Request::Create { id, .. }
            | Request::Settle { id, .. }
            | Request::Listen { id, .. } => *id,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub struct Record {
    pub id: PromiseId,
    pub state: PromiseState,
    pub value: Value,
    pub timeout_at: Time,
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub struct Response {
    pub status: u16,
    pub promise: Option<Record>,
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub struct Call {
    pub client: ClientId,
    pub id: CallId,
    pub requested_at: Time,
    pub request: Request,
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Output {
    Response {
        client: ClientId,
        id: CallId,
        response: Response,
    },
    Notification {
        address: Address,
        promise: Record,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Structural, Hash, PartialOrd, Ord, Debug)]
pub enum Message {
    Request(Call),
    Output(Output),
}

} // verus!

impl Clone for Promises {
    fn clone(&self) -> Self {
        match self {
            Promises::Nil => Promises::Nil,
            Promises::Cons(promise, rest) => Promises::Cons(*promise, Box::new((**rest).clone())),
        }
    }
}

impl Clone for State {
    fn clone(&self) -> Self {
        Self {
            promises: self.promises.clone(),
        }
    }
}
