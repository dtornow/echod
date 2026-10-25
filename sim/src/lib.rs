//! echod-sim: the node under deterministic simulation.
//!
//! One process, one seed, no wall clock and no sockets. The simulation owns
//! every input a node has — the clock, the object store, the message bus,
//! and when a node dies — and the same seed replays the same
//! run, which is what makes a failure something to fix rather than something
//! to remember.
//!
//! ```text
//! rng.rs       the one source of randomness, seeded
//! clock.rs     virtual time: tokio's paused clock, read through the Clock port
//! store.rs     an in-memory S3 that misbehaves on request
//! bus.rs       a bus that records every message and checks it against the bucket
//! history.rs   what each client saw and what the nodes did, with virtual timestamps
//! workload.rs  the requests a run issues, and how they are generated
//! checker.rs   the run as a trace of the Resonate model, checked by accordant
//! sim.rs       the run: nodes over one store, clients, crashes, then the checks
//! ```
//!
//! The specification a run is checked against is the Resonate model of
//! `dtornow/accordant`, the whole protocol as the Lean specification has it,
//! and the checker is accordant's: some execution of the model must show
//! exactly what the clients saw and the bus carried, with the nodes' own
//! steps (a sweep, a fire) where the nodes report them (`checker.rs`). The
//! run ends with a read of every id, so the state the bucket holds is what
//! the model holds too. Besides: every deadline a document owes has a key;
//! every message names state that is really there; and the run exercised
//! what it claims to have exercised.

pub mod bus;
pub mod checker;
pub mod clock;
pub mod history;
pub mod rng;
pub mod sim;
pub mod store;
#[path = "../../diff/accordant/src/wire.rs"]
pub mod wire;
pub mod workload;
