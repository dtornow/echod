//! A Rust + Verus Rover world.
//!
//! - [`comm`] contains values shared by specifications and executable tests.
//! - [`spec`] contains stateful mathematical processes, world semantics, and
//!   refinement.
//! - [`test`] contains executable realizations, bounded search, and verified
//!   replay.

pub mod comm;
pub mod spec;
pub mod test;

// Convenient facade; layer-specific imports remain available.
pub use comm::{BoundaryEvent, Envelope, ProcessEvent};
pub use spec::{refinement, EventOf, RoverModel, RoverProc, RoverSpec};
pub use test::{
    check, replay, search, Action, BoundaryOf, Certificate, CheckConfig, ConfigOf,
    ExecEventOf, ExecProcOf, MessageOf, PidOf, ProcOf, ProcResult, RoverExec,
    RoverProcExec, SpecOf, StepResult,
};
