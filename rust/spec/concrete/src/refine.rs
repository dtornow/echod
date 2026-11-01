//! The abstract model this specification refines.
//!
//! Concrete depends on `resonate` for that refinement. The simulation is the
//! open proof: a bucket whose changed document is `spec_promise_create` is
//! related to a server after `promise_create_v`, and the same for every other
//! handler. Naming the abstract server is the dependency.

/// The abstract Resonate server, `echod-abstract`.
pub fn abstract_server() -> &'static str {
    std::any::type_name::<resonate::Resonate>()
}
