//! The nodes reach each other in process: a forwarded request is a call.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, Weak};

use async_trait::async_trait;
use echod_server::env::Peers;
use echod_server::Server;
use resonate_core::types::{RequestEnvelope, ResponseEnvelope};
use resonate_core::Unavailable;

#[derive(Default)]
pub struct SimPeers {
    by_url: Mutex<BTreeMap<String, Weak<Server>>>,
}

impl SimPeers {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&self, url: &str, server: &Arc<Server>) {
        self.by_url.lock().unwrap().insert(url.to_string(), Arc::downgrade(server));
    }

    pub fn unregister(&self, url: &str) {
        self.by_url.lock().unwrap().remove(url);
    }
}

#[async_trait]
impl Peers for SimPeers {
    async fn forward(&self, url: &str, _from: &str, req: &RequestEnvelope) -> Result<ResponseEnvelope, Unavailable> {
        let server = self.by_url.lock().unwrap().get(url).and_then(Weak::upgrade);
        let Some(server) = server else { return Err(Unavailable::new(format!("no node at {url}"))) };
        tokio::task::yield_now().await;
        let mut crashed = server.crashed();
        tokio::select! {
            biased;
            _ = crashed.changed() => Err(Unavailable::new("owner crashed")),
            r = server.process_from(req, true) => r.map(|(resp, _)| resp),
        }
    }
}
