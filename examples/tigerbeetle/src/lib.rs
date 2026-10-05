//! TigerBeetle's state machine as a lean accordant model: accounts, transfers,
//! two-phase transfers and their expiry. Read from tigerbeetle/tigerbeetle
//! (`src/tigerbeetle.zig`, `src/state_machine.zig`).
//!
//! * `spec`: the data model: the state, the requests, the responses, the
//!   internal work. The steps come next.

pub mod spec;

pub use spec::*;
