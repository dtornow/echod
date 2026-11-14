//! `POST /`, `GET /ready` and `GET /metrics`.
//!
//! Bytes become an envelope and go to the node; the answer's `head.status`
//! becomes the HTTP status. `Unavailable` is a 503. Every answer carries
//! `x-echod-node`.

use std::net::SocketAddr;
use std::sync::Arc;

use axum::body::Bytes;
use axum::extract::State;
use axum::http::{HeaderValue, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use resonate_core::types::{parse_and_validate, salvage_context, ResponseEnvelope};
use resonate_core::ResonateServer;

use crate::node::{Node, NODE};

pub fn app(server: Arc<Node>) -> Router {
    Router::new().route("/", post(handle)).route("/ready", get(ready)).route("/metrics", get(metrics)).with_state(server)
}

async fn metrics(State(server): State<Arc<Node>>) -> Response {
    let body = server.metrics().encode();
    ([(axum::http::header::CONTENT_TYPE, crate::metrics::CONTENT_TYPE)], body).into_response()
}

async fn ready(State(server): State<Arc<Node>>) -> StatusCode {
    if server.ready().await {
        StatusCode::OK
    } else {
        StatusCode::SERVICE_UNAVAILABLE
    }
}

async fn handle(State(server): State<Arc<Node>>, body: Bytes) -> Response {
    let resp = match parse_and_validate(&body) {
        Err(e) => {
            let (kind, corr) = salvage_context(&body);
            server.metrics().request(&kind, 400, std::time::Instant::now());
            ResponseEnvelope::error(kind, corr, 400, &e.to_string())
        }
        Ok(req) => match server.process(&req).await {
            Ok(resp) => resp,
            Err(e) => {
                tracing::warn!(kind = %req.kind, error = %e, "unavailable");
                ResponseEnvelope::error(req.kind.clone(), req.head.corr_id.clone(), 503, &e.message)
            }
        },
    };
    let code = StatusCode::from_u16(resp.head.status as u16).unwrap_or(StatusCode::INTERNAL_SERVER_ERROR);
    let mut r = (code, Json(resp)).into_response();
    if let Ok(v) = HeaderValue::from_str(server.id()) {
        r.headers_mut().insert(NODE, v);
    }
    r
}

/// Serve until `shutdown` says so. Returns the address bound.
pub async fn serve(server: Arc<Node>, bind: &str, mut shutdown: tokio::sync::watch::Receiver<bool>) -> std::io::Result<(SocketAddr, tokio::task::JoinHandle<()>)> {
    let listener = tokio::net::TcpListener::bind(bind).await?;
    let addr = listener.local_addr()?;
    let app = app(server);
    let handle = tokio::spawn(async move {
        let _ = axum::serve(listener, app)
            .with_graceful_shutdown(async move {
                let _ = shutdown.changed().await;
            })
            .await;
    });
    Ok((addr, handle))
}
