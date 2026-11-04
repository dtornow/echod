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
//! `Output` out. Store traffic and `Stop` observe as nothing. The concrete
//! node view carries the cached documents, the open flight, and the
//! occurrences still owed, so a relation can name them. A retry offers
//! `Dispatch::Execute` and a settled listener sends `Dispatch::Unblock`, the
//! same boundary outputs the abstract model sends.
//!
//! `spec_on_event` on each model is that model's step. The executable
//! `on_event` is obliged to agree with it; that equality is not proved.
//! A lease sets the next offer to the deadline on the abstract model and to
//! `now` on this one, and an abstract retry lands on the `next_offer` grid
//! while this plane uses `now + 5000`.

/// The abstract Resonate model, `echod-abstract`.
pub fn abstract_model() -> &'static str {
    std::any::type_name::<echod_abstract::Model>()
}
