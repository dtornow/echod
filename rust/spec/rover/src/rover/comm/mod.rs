//! Values shared by mathematical Rover specifications and executable tests.

use vstd::prelude::*;

use crate::Time;

verus! {

/// A message in Rover's append-only network.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Envelope<P, M> {
    pub sender: P,
    pub recipient: P,
    pub message: M,
}

/// What one process receives.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProcessEvent<P, M> {
    Receive { sender: P, message: M },
    Timeout,
}

/// An event at the system boundary.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum BoundaryEvent<P, M> {
    Input { recipient: P, at: Time, message: M },
    Output { sender: P, at: Time, message: M },
}

impl<P, M> BoundaryEvent<P, M> {
    /// The world's monotone time attached to this boundary event.
    pub fn time(&self) -> Time {
        match self {
            BoundaryEvent::Input { at, .. } | BoundaryEvent::Output { at, .. } => *at,
        }
    }
}

} // verus!
