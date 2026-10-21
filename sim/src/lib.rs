//! echod-sim: the server under deterministic simulation.
//!
//! One process, one seed, no wall clock and no sockets. The simulation owns
//! every input the server has — the clock, the object store, the other nodes,
//! the message bus, and when a node dies — and the same seed replays the same
//! run, which is what makes a failure something to fix rather than something
//! to remember.
//!
//! ```text
//! rng.rs       the one source of randomness, seeded
//! clock.rs     virtual time: tokio's paused clock, read through the Clock port
//! store.rs     an in-memory S3 that misbehaves on request
//! peers.rs     the nodes reach each other in process
//! bus.rs       a bus that records every message and checks it against the bucket
//! history.rs   what each client and each sweep saw, with virtual timestamps
//! workload.rs  the requests a run issues, and how they are generated
//! model.rs     the specification: the kernel, one operation at a time
//! checker.rs   linearizability of a history against the model, per document
//! sim.rs       the run: servers over one store, clients, crashes, then the checks
//! ```
//!
//! What a run checks: that the recorded history is equivalent to some
//! sequential execution of the kernel which also leaves the state the bucket
//! holds; that every deadline a document owes has a key; that every message
//! names state that is really there; and that the run exercised what it
//! claims to have exercised.

pub mod bus;
pub mod checker;
pub mod clock;
pub mod history;
pub mod model;
pub mod peers;
pub mod rng;
pub mod sim;
pub mod store;
pub mod workload;
