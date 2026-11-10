//! Values shared by mathematical Rover specifications and executable tests.

use vstd::prelude::*;

use std::fmt::Debug;
use std::hash::Hash;

verus! {

pub trait Data: Clone + Eq + Hash + Ord + Debug {}
impl<T: Clone + Eq + Hash + Ord + Debug> Data for T {}

pub type Time = u64;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Sched<T> {
    Later(T),
    Timer(Time, T),
}

impl<T> Sched<T> {
    pub fn req(&self) -> (request: &T)
        ensures
            *request == match *self {
                Sched::Later(request) | Sched::Timer(_, request) => request,
            },
    {
        match self {
            Sched::Later(request) | Sched::Timer(_, request) => request,
        }
    }
}

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
    Clock { at: Time },
}

impl<P, M> BoundaryEvent<P, M> {
    /// The world's monotone time attached to this boundary event.
    pub fn time(&self) -> Time {
        match self {
            BoundaryEvent::Input { at, .. }
            | BoundaryEvent::Output { at, .. }
            | BoundaryEvent::Clock { at } => *at,
        }
    }
}

} // verus!

impl<T> Sched<T> {
    pub fn due(&self) -> Option<Time> {
        match self {
            Sched::Later(_) => None,
            Sched::Timer(at, _) => Some(*at),
        }
    }

    pub fn ready(&self, now: Time) -> bool {
        match self {
            Sched::Later(_) => true,
            Sched::Timer(at, _) => *at <= now,
        }
    }

    pub fn at(self, _now: Time) -> Self {
        self
    }
}
