//! Messages out: HTTP push, and the router in front of it.
//!
//! A message is POSTed to the worker's URL as the JSON `Message` the protocol
//! defines. Delivery is at most once: a failure is logged and dropped, and a
//! lost `execute` is re-emitted by the task's retry deadline.

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;
use resonate_core::types::Message;
use resonate_core::{scheme_of, ResonateRouter, ResonateWorker, Unavailable};

pub struct HttpPush {
    client: reqwest::Client,
}

impl HttpPush {
    pub fn new() -> Self {
        let client = reqwest::Client::builder().connect_timeout(Duration::from_secs(5)).timeout(Duration::from_secs(30)).build().expect("an HTTP client");
        Self { client }
    }
}

impl Default for HttpPush {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl ResonateWorker for HttpPush {
    async fn process(&self, address: &str, msg: &Message) -> Result<(), Unavailable> {
        let resp = self.client.post(address).json(msg).send().await.map_err(|e| Unavailable::new(format!("push to {address}: {e}")))?;
        if !resp.status().is_success() {
            return Err(Unavailable::new(format!("push to {address}: HTTP {}", resp.status())));
        }
        Ok(())
    }
}

/// One worker per address scheme.
pub struct Router {
    workers: HashMap<String, Arc<dyn ResonateWorker>>,
}

impl Router {
    pub fn new() -> Self {
        Self { workers: HashMap::new() }
    }

    pub fn with(mut self, scheme: &str, worker: Arc<dyn ResonateWorker>) -> Self {
        self.workers.insert(scheme.to_string(), worker);
        self
    }

    /// The router every node runs: HTTP push for `http` and `https`.
    pub fn http_push() -> Self {
        let push: Arc<dyn ResonateWorker> = Arc::new(HttpPush::new());
        Self::new().with("http", Arc::clone(&push)).with("https", push)
    }
}

impl Default for Router {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl ResonateRouter for Router {
    async fn route(&self, address: &str, msg: &Message) -> Result<(), Unavailable> {
        let scheme = scheme_of(address).ok_or_else(|| Unavailable::unroutable(format!("not an address: {address}")))?;
        let worker = self.workers.get(scheme.as_str()).ok_or_else(|| Unavailable::unroutable(format!("no worker for {scheme}://")))?;
        worker.process(address, msg).await
    }
}
