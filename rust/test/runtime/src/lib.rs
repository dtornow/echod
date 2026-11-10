//! echod-sim: the node under deterministic simulation.
//!
//! One system, one seed, no runtime, wall clock, threads, or sockets. An
//! explicit event loop owns every input to the production decision core:
//! clocks, store completions, wakes, requests, chaos, and node lifecycle.
//! The same seed replays the same
//! run, which is what makes a failure something to fix rather than something
//! to remember.
//!
//! ```text
//! rng.rs       the one source of randomness, seeded
//! store.rs     the production concrete in-memory store with seeded faults
//! history.rs   what each client saw and what the nodes did, with virtual timestamps
//! workload.rs  the requests a run issues, and how they are generated
//! checker.rs   the run as a trace of the Resonate model, checked by Rover
//! rover_sim.rs isolated `RoverExec::exec` experiment over production-backed concrete processes
//! sim.rs       the deterministic event loop, clients, nodes, chaos, and checks
//! ```
//!
//! The specification a run is checked against is the Resonate model,
//! the whole protocol as the Lean specification has it,
//! and the checker is Rover's: some execution of the model must show
//! exactly what the clients saw and the nodes emitted, with the nodes' own
//! steps (a sweep, a fire) where the nodes report them (`checker.rs`). The
//! run ends with a read of every id, so the state the bucket holds is what
//! the model holds too. Besides: every deadline a document owes has a key;
//! every message names state that is really there; and the run exercised
//! what it claims to have exercised.

pub mod checker;
pub mod history;
pub mod rng;
pub mod rover_sim;
pub mod sim;
pub mod store;
pub mod workload;
