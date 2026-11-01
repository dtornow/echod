//! echod: the node. The decision core (`echod-logic`) run against a real
//! store, a real clock and HTTP.
//!
//! ```text
//! config.rs     the dials
//! store.rs      the object store port: `object_store` behind it, S3 Express on the SDK for appends, an in-memory model
//! env.rs        the clock and the listener, as ports
//! node.rs       the executor: the core's effects, performed; the `ResonateServer`
//! push.rs       messages out: HTTP push, and the router in front of it
//! gateway.rs    `POST /`, `GET /ready` and `GET /metrics`
//! metrics.rs    what an operator sees: OpenMetrics, with labels from closed sets only
//! ```

pub mod config;
pub mod env;
pub mod gateway;
pub mod metrics;
pub mod node;
pub mod push;
pub mod store;

pub use config::Config;
pub use node::Node;
