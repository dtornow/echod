//! What the server takes from outside the store: the clock, and the other
//! nodes. Both are ports so a simulation can own them.

use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;
use resonate_core::types::{RequestEnvelope, ResponseEnvelope};
use resonate_core::Unavailable;
use serde_json::json;

/// Wall time in ms, or whatever stands in for it.
pub trait Clock: Send + Sync {
    fn now(&self) -> u64;
}

/// The system clock, monotone.
pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> u64 {
        resonate_core::util::system_time_ms().max(0) as u64
    }
}

/// The other nodes, as a request can be handed to one of them.
#[async_trait]
pub trait Peers: Send + Sync {
    /// Run `req` at the node serving `url`, as a request forwarded by `from`.
    async fn forward(&self, url: &str, from: &str, req: &RequestEnvelope) -> Result<ResponseEnvelope, Unavailable>;
}

/// The header a forwarded request carries, so the owner never forwards it on.
pub const FORWARDED: &str = "x-echod-forwarded";

/// The nodes over HTTP.
pub struct HttpPeers {
    client: reqwest::Client,
}

impl HttpPeers {
    pub fn new() -> Self {
        Self { client: reqwest::Client::builder().connect_timeout(Duration::from_secs(2)).timeout(Duration::from_secs(30)).build().expect("an HTTP client") }
    }
}

impl Default for HttpPeers {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl Peers for HttpPeers {
    async fn forward(&self, url: &str, from: &str, req: &RequestEnvelope) -> Result<ResponseEnvelope, Unavailable> {
        let body = json!({
            "kind": req.kind,
            "head": { "corrId": req.head.corr_id, "version": req.head.version, "auth": req.head.auth, "resonate:debug_time": req.head.debug_time },
            "data": req.data,
        });
        let resp = self.client.post(url).header(FORWARDED, from).json(&body).send().await.map_err(|e| Unavailable::new(e.to_string()))?;
        if resp.status().as_u16() == 503 {
            return Err(Unavailable::new("owner unavailable"));
        }
        #[derive(serde::Deserialize)]
        struct Wire {
            kind: String,
            head: Head,
            data: serde_json::Value,
        }
        #[derive(serde::Deserialize)]
        struct Head {
            #[serde(rename = "corrId")]
            corr_id: String,
            status: i32,
        }
        let w: Wire = resp.json().await.map_err(|e| Unavailable::new(e.to_string()))?;
        Ok(ResponseEnvelope::new(w.kind, w.head.corr_id, w.head.status, w.data))
    }
}

pub type SharedClock = Arc<dyn Clock>;

/// What a simulation watches: the internal steps a node runs on its own,
/// which no client sees but which a model must account for.
pub trait Observer: Send + Sync {
    /// A sweep of `origin` at `now` starts on `node`. Returns a handle for `sweep_end`.
    fn sweep_begin(&self, node: &str, origin: &str, now: u64) -> u64 {
        let _ = (node, origin, now);
        0
    }
    /// The sweep ended; `committed` says whether it landed.
    fn sweep_end(&self, handle: u64, committed: bool) {
        let _ = (handle, committed);
    }
}

/// Watches nothing.
pub struct NoObserver;

impl Observer for NoObserver {}
