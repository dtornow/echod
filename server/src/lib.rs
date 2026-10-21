//! echod-server: the Resonate protocol over an S3 bucket.
//!
//! ```text
//! config.rs     the dials
//! keys.rs       where everything lives under the bucket
//! store.rs      the object store port: `object_store` behind it, S3 Express on the SDK for appends, an in-memory model
//! doc.rs        a document, an origin's or a schedule's: rows in, rows out, the fold between
//! env.rs        the clock and the other nodes, as ports
//! wire.rs       the kernel's vocabulary to the protocol's and back
//! nodes.rs      the nodes: announce, heartbeat, list, and who owns what
//! cache.rs      what a node remembers: documents by LRU under a byte budget
//! applier.rs    one step against one document, serialised and committed: the verified commit, run against the store; the fire across two
//! timers.rs     deadlines as objects in time buckets, fired by the owner from memory
//! push.rs       messages out: HTTP push, and the router in front of it
//! server.rs     the `ResonateServer`: dispatch, forwarding, lifecycle
//! gateway.rs    `POST /`, `GET /ready` and `GET /metrics`
//! metrics.rs    what an operator sees: OpenMetrics, with labels from closed sets only
//! ```

pub mod applier;
pub mod cache;
pub mod config;
pub mod doc;
pub mod env;
pub mod gateway;
pub mod keys;
pub mod metrics;
pub mod nodes;
pub mod push;
pub mod server;
pub mod store;
pub mod timers;
pub mod wire;

pub use config::Config;
pub use server::Server;
