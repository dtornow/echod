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
//! checker.rs   bounded finite-trace search over the workspace Abstract model
//! wire.rs      local Abstract-to-protocol conversion
//! sim.rs       the run: nodes over one store, clients, crashes, then the checks
//! ```
//!
//! The specification is the workspace `echod-abstract` executable machine.
//! The local checker searches call linearizations and productive internal
//! actions, and reports `Unknown` rather than accepting when its finite
//! budget is exhausted. The run ends with a read of every id, so the bucket's
//! visible state is checked too.

pub mod bus;
pub mod checker;
pub mod clock;
pub mod history;
pub mod rng;
pub mod sim;
pub mod store;
pub mod wire;
pub mod workload;
