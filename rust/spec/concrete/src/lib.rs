//! The tie from the running process down to the Rover abstract model.
//!
//! `echod_logic::State::on_event` is the process. `resonate` is the abstract
//! model. What belongs here, and is not written yet, is a view of that state,
//! a proof that `on_event` implements the concrete transition, and the
//! boundary-trace refinement that follows from Rover's theorem.

use echod_logic::State;
use resonate::Resonate;

/// Names the two ends of the refinement so the dependency is real.
pub fn endpoints() -> (&'static str, &'static str) {
    (std::any::type_name::<State>(), std::any::type_name::<Resonate>())
}
