//! echod-server: the Resonate protocol over an S3 bucket.
//!
//! ```text
//! config.rs     the dials
//! keys.rs       where everything lives under the bucket
//! store.rs      the object store port: S3, and an in-memory stand-in
//! doc.rs        an origin's document: rows in, rows out, the fold between
//! wire.rs       the kernel's vocabulary to the protocol's and back
//! nodes.rs      the nodes: announce, heartbeat, list, and who owns what
//! applier.rs    one request against one origin, serialised and committed
//! timers.rs     deadlines as objects, fired by the owner
//! schedules.rs  schedules as objects, fired by the owner
//! push.rs       messages out: HTTP push, and the router in front of it
//! server.rs     the `ResonateServer`: dispatch, forwarding, lifecycle
//! gateway.rs    `POST /` and `GET /ready`
//! ```

pub mod applier;
pub mod config;
pub mod doc;
pub mod gateway;
pub mod keys;
pub mod nodes;
pub mod push;
pub mod schedules;
pub mod server;
pub mod store;
pub mod timers;
pub mod wire;

pub use config::Config;
pub use server::Server;
