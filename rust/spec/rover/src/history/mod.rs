//! Linearization-history search and certified replay.
//!
//! This is the client-history checker used by the simulator and model driver.
//! It is distinct from [`crate::rover`], the message-passing world used for
//! process refinement.

pub mod certificate;
mod checker;
mod drive;
mod sim;
pub mod semantics;

pub use certificate::{certify, marks, Certificate, Silent};
pub use checker::{Checker, Config, Factor, Node, Pending, Stats, Verdict, Violation};
pub use drive::{drive, Choice, Choices, Drive, Run, Tried};
pub use sim::Sim;
