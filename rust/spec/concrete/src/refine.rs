//! The statement this crate is for.
//!
//! Instantiate Rover with this crate's model — the nodes, each with its own memory,
//! `spec_world` at the start, `spec_step` at every process — and with the
//! abstract model, the one service. The concrete instantiation refines the
//! abstract one:
//!
//! ```text
//! echod_rover::rover::refinement::refines(
//!     echod_concrete::Model,
//!     concrete_config,
//!     resonate::abstract_model::Model,
//!     abstract_config,
//! )
//! ```
//!
//! That is every boundary trace of the concrete world is a boundary trace of
//! the abstract world. `concrete_refines_abstract` is how it is proved, from
//! a relation on the two initial worlds and a forward simulation. The
//! theorem is stated at one boundary, `resonate::BoundaryEvent`. The relation
//! and the simulation are not proved yet. `spec_logic_on_event` is the node
//! step inside the concrete instantiation; `spec_promise_create` is what that
//! step cites for one request.

/// The abstract Resonate model, `echod-abstract`.
pub fn abstract_model() -> &'static str {
    std::any::type_name::<resonate::abstract_model::Model>()
}
