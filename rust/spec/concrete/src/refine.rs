//! Refinement of this model to the abstract one.
//!
//! The concrete world is the nodes and the store. The abstract world is the
//! one service. They share no handlers. Every boundary trace of the concrete
//! world is a boundary trace of the abstract world.
//! `simulation::lemma_refines` is that statement, once `output_simulation`
//! holds, by `concrete_refines_abstract`.
//!
//! Both models observe `echod_abstract::BoundaryEvent`: a `Call` in, an
//! `Output` out. An injected `Request` is one abstract input of that call
//! to the service. `Stop` and store traffic observe as nothing, so the
//! matching abstract execution is empty. An observed `Output` is one abstract
//! outside step of that output. A process step observes nothing. One that
//! sends no output to the outside is an empty abstract execution. One that
//! sends an output is `output_simulation`: a finite abstract execution whose
//! boundary projection is empty and which leaves the two worlds related.
//! The trait's `ensures` on `on_event` states that the executable results
//! equal `spec_on_event`. That proof is separate from this simulation.
//!
//! The concrete node view carries the cached documents, the open flight, and
//! the occurrences still owed. A retry offers `Dispatch::Execute` and a
//! settled listener sends `Dispatch::Unblock`, the same boundary outputs the
//! abstract model sends. A lease timeout offers the task again at `now`, and
//! a retry offers it again at `now + retryTimeout`, on both models. A read
//! projects for the answer and writes the document only when the handler
//! writes. A promise is awaitable when it has a target,
//! `resonate:scope=global`, `resonate:external=true`, or a timer. A fence
//! that names another origin is refused. A schedule is refused only when its
//! promises are a timer with a target. The proofs are the bodies in
//! `simulation`. Cargo erases them.

/// The abstract Resonate model, `echod-abstract`.
pub fn abstract_model() -> &'static str {
    std::any::type_name::<echod_abstract::Model>()
}
