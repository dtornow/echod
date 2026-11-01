//! The one step a node takes.
//!
//! The process implements that step as `State::on_event`: an event in, the
//! effects it asks for out. This crate does not depend on the process, so the
//! step is named here in the document's vocabulary. A request whose document
//! is loaded runs the sweep, then `spec_handle`, then the drain. A promise
//! create inside that step is `spec_promise_create`. The store applies the
//! `Store` effect the step already produced.

use vstd::prelude::*;

use crate::types::*;

verus! {

/// What a node is told. The clock is the node's, read when the event happened.
#[cfg(verus_keep_ghost)]
pub enum Step {
    Start { clock: nat, loops: bool },
    /// A request whose document is in hand. `spec_handle` is the document half.
    Request { request: ARequest, clock: nat },
    /// A store call this node issued has an answer.
    Completed { clock: nat },
    Tick { clock: nat },
    Stop { clock: nat },
}

} // verus!
