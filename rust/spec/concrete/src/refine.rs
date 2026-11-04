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
//! A lease timeout offers the task again at `now`, and a retry offers it
//! again at `now + retryTimeout`, on both models. A read projects for the
//! answer and writes the document only when the handler writes. A promise is
//! awaitable when it has a target, `resonate:scope=global`,
//! `resonate:external=true`, or a timer. A fence that names another origin
//! is refused. A schedule is refused only when its promises are a timer with
//! a target. The simulation is not proved.

/// The abstract Resonate model, `echod-abstract`.
pub fn abstract_model() -> &'static str {
    std::any::type_name::<echod_abstract::Model>()
}
