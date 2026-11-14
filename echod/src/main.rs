use std::sync::Arc;

use clap::Parser;
use echod::{gateway, store, Config, Node};
use resonate_core::ResonateServer;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt().with_env_filter(tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into())).init();
    let cfg = Config::parse();
    let store = match store::open(&cfg).await {
        Ok(s) => s,
        Err(e) => {
            tracing::error!(error = %e, "could not open the store");
            std::process::exit(1);
        }
    };
    let server = Node::new(cfg.clone(), store);
    if let Err(e) = server.init(false).await {
        tracing::error!(error = %e, "could not start");
        std::process::exit(1);
    }
    let (tx, rx) = tokio::sync::watch::channel(false);
    let (addr, serving) = match gateway::serve(Arc::clone(&server), &cfg.bind, rx).await {
        Ok(x) => x,
        Err(e) => {
            tracing::error!(error = %e, bind = %cfg.bind, "could not listen");
            std::process::exit(1);
        }
    };
    tracing::info!(node = %server.id(), url = %server.url(), %addr, "serving");
    let _ = tokio::signal::ctrl_c().await;
    tracing::info!("stopping");
    let _ = server.stop().await;
    let _ = tx.send(true);
    let _ = serving.await;
}
