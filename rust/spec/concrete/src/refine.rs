//! Refinement of this model to the abstract one.
//!
//! The concrete world is the nodes and the store. The abstract world is the
//! one service. They share no handlers. The statement is that every boundary
//! trace of the concrete world is a boundary trace of the abstract world:
//!
//! ```text
//! echod_rover::rover::refinement::concrete_refines_abstract(
//!     echod_concrete::Model,
//!     concrete_config,
//!     echod_abstract::Model,
//!     abstract_config,
//! )
//! ```
//!
//! Both models observe `echod_abstract::BoundaryEvent`: a `Call` in, an
//! `Output` out. The theorem needs a relation on the two initial worlds and
//! a forward simulation. Neither is proved yet. The concrete view does not
//! yet carry the node's documents.

/// The abstract Resonate model, `echod-abstract`.
pub fn abstract_model() -> &'static str {
    std::any::type_name::<echod_abstract::Model>()
}
