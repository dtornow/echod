//! The store machine, `Concrete`: what echod does to the bucket on a request
//! and on a sweep, as an `accordant::Model`, so that its traces are judged by
//! the same semantics as the Resonate model's. Then the theorem this crate is
//! for, `concrete_refines_abstract`: every trace of the store machine is a
//! trace of the Resonate model.
//!
//! The state is the bucket's documents, the kernel's own `AState`. A request
//! is what `logic::flight::decide` does: the wire rules of `dispatch.rs`, a
//! sweep of the document at the request's instant, the kernel handler
//! (`spec_handle`, the kernel's own functional specification), a drain. A
//! sweep is internal work, due at the state's next deadline, as the key a
//! commit arms. The outbox a step leaves is what it sends.
//!
//! The sweep is a function here (`sweep_fn`): the kernel specifies `sweep`
//! and `drain` relationally, as some chain of legal steps that leaves nothing
//! due, and three of its six step functions functionally; the fold below runs
//! the six in the order the Resonate model runs them, which reaches the
//! fixpoint in one pass. That the kernel's executable sweep computes this fold
//! is not proved here: the one gap between the store machine and the code,
//! beside the glue every model has.
//!
//! Verified with `cargo verus verify -p echod-refine`; empty under plain
//! `cargo build`.

#![cfg(verus_keep_ghost)]
#![allow(unused_imports)]

pub mod machine;
pub mod translate;
pub mod sweep;
pub mod sweep_proof;
pub mod canon;
pub mod absorb;
pub mod onstep;
pub mod trans;
pub mod drain;
pub mod frame;
pub mod effect;
pub mod tagsv;
pub mod hcommon;
pub mod hmany;
pub mod handlers;
pub mod tick;
pub mod theorem;
