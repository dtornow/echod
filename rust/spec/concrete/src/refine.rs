//! Refinement of this model to the abstract one.
//!
//! The concrete world is the nodes and the store. The abstract world is the
//! one service. They share no handlers. Every boundary trace of the concrete
//! world is a boundary trace of the abstract world.
//! `simulation::lemma_refines` is that statement, by
//! `concrete_refines_abstract`, at the abstract configuration the fleet
//! implements (`relation::abstract_config`: the fleet's retry timeout). It
//! assumes nothing: `relation::agreement`,
//! that every handler, the due step, and the occurrence do the same on a
//! document and on the abstract store it reads as, is proved in `interpret`,
//! `handlers`, and `timers`. A 503 for a call still on the network is one
//! abstract shed, and an empty-task heartbeat is one abstract serve of
//! status 200.
//!
//! Both models observe `echod_abstract::BoundaryEvent`: a `Call` in, an
//! `Output` out. An injected `Request` is one abstract input of that call
//! to the service. `Stop` and store traffic observe as nothing, so the
//! matching abstract execution is empty. An observed `Output` is one abstract
//! outside step of that output. A process step observes nothing. One that
//! sends no output to the outside is an empty abstract execution. The step
//! that begins a flight is one abstract step, taken on the owners' caches;
//! the store steps and the reply that closes the flight are stutters.
//! The theorem is about the distinct abstract and concrete `Spec` types.
//! Each executable `Model` implements `RoverExec::Spec`; the trait's
//! contracts prove that `initial` realizes `processes`, while each
//! `RoverExec::Proc::on_event` realizes `RoverSpec::Proc::on_event`.
//! Verus checks those bridges, node (`Node::step`) and store
//! (`Store::step`) alike. The concrete node trusts its JSON codec, its
//! key hash, its string characters, and the abstract crate's cron engine and
//! id template; `node.rs` names them.
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
    std::any::type_name::<echod_abstract::Spec>()
}
