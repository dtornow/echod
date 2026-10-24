//! What both harnesses share: the server processes, the sink the workers'
//! messages are pushed to, and the client that speaks the protocol over HTTP.

use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use axum::routing::post;
use axum::{Json, Router};
use resonate_core::types::PROTOCOL_VERSION;
use serde_json::{json, Value};

// ---------------------------------------------------------------------------
// The processes, the sink, the client
// ---------------------------------------------------------------------------

pub fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

pub struct Server {
    pub name: &'static str,
    pub url: String,
    child: Child,
}

impl Drop for Server {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

pub fn spawn(name: &'static str, mut cmd: Command, url: String, logs: &PathBuf) -> Server {
    std::fs::create_dir_all(logs).expect("a log directory");
    let out = std::fs::File::create(logs.join(format!("{name}.log"))).expect("a log file");
    let err = out.try_clone().expect("a log file");
    // The servers push to the sink on localhost: no proxy may stand between.
    for v in ["HTTP_PROXY", "HTTPS_PROXY", "http_proxy", "https_proxy", "ALL_PROXY", "all_proxy"] {
        cmd.env_remove(v);
    }
    let child = cmd.stdout(Stdio::from(out)).stderr(Stdio::from(err)).stdin(Stdio::null()).spawn().unwrap_or_else(|e| panic!("cannot start {name}: {e}"));
    Server { name, url, child }
}

/// The messages pushed to the harness's worker, in the order they came.
#[derive(Default)]
pub struct Sink {
    pub got: Mutex<Vec<Value>>,
}

impl Sink {
    pub fn count(&self) -> usize {
        self.got.lock().unwrap().len()
    }
    pub fn take(&self) -> Vec<Value> {
        self.got.lock().unwrap().drain(..).collect()
    }
}

pub async fn start_sink(sink: Arc<Sink>) -> String {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let url = format!("http://127.0.0.1:{}/", listener.local_addr().unwrap().port());
    let app = Router::new().route(
        "/",
        post(move |Json(v): Json<Value>| {
            let sink = Arc::clone(&sink);
            async move {
                sink.got.lock().unwrap().push(v);
                axum::http::StatusCode::OK
            }
        }),
    );
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    url
}

pub struct Client {
    http: reqwest::Client,
}

impl Client {
    pub fn new() -> Self {
        Self { http: reqwest::Client::builder().no_proxy().timeout(Duration::from_secs(30)).build().expect("an HTTP client") }
    }

    pub async fn send(&self, s: &Server, kind: &str, data: &Value, now: i64, corr: &str) -> (u16, Value) {
        let body = json!({ "kind": kind, "head": { "corrId": corr, "version": PROTOCOL_VERSION, "resonate:debug_time": now }, "data": data });
        let resp = self.http.post(&s.url).json(&body).send().await.unwrap_or_else(|e| panic!("{}: no answer for {kind}: {e}", s.name));
        let status = resp.status().as_u16();
        let v: Value = resp.json().await.unwrap_or_else(|e| panic!("{}: not an envelope for {kind}: {e}", s.name));
        let head_status = v["head"]["status"].as_u64().map(|s| s as u16).unwrap_or(status);
        (head_status, v["data"].clone())
    }

    pub async fn wait_ready(&self, s: &Server) {
        let start = Instant::now();
        loop {
            let body = json!({ "kind": "promise.get", "head": { "corrId": "ready", "version": PROTOCOL_VERSION, "resonate:debug_time": 1 }, "data": { "id": "ready:probe" } });
            if let Ok(r) = self.http.post(&s.url).json(&body).send().await {
                if r.status().as_u16() < 500 {
                    return;
                }
            }
            assert!(start.elapsed() < Duration::from_secs(60), "{} did not come up at {}", s.name, s.url);
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    }
}


/// Start echod in debug mode: the clock is the request's, nothing runs on
/// its own. `retry_timeout` in ms.
pub fn spawn_echod(bin: &PathBuf, server_url: &str, retry_timeout: u64, logs: &PathBuf) -> Server {
    let port = free_port();
    let mut cmd = Command::new(bin);
    cmd.args(["--debug", "--bind", &format!("127.0.0.1:{port}"), "--url", server_url, "--node-id", "diff", "--retry-timeout", &retry_timeout.to_string(), "--compact", "0"]);
    cmd.env("RUST_LOG", "warn");
    spawn("echod", cmd, format!("http://127.0.0.1:{port}/"), logs)
}

/// Start the reference server in debug mode, SQLite in memory, its other
/// gateways off.
#[allow(dead_code)]
pub fn spawn_reference(bin: &PathBuf, port: u16, server_url: &str, logs: &PathBuf) -> Server {
    let mut cmd = Command::new(bin);
    cmd.args(["dev", "--debug", "--level", "warn", "--server-bind", "127.0.0.1", "--server-port", &port.to_string(), "--server-url", server_url, "--tasks-retry-timeout", "30000", "--console-enabled", "false", "--observability-metrics-enabled", "false", "--transports-http-poll-enabled", "false"]);
    spawn("resonate", cmd, format!("http://127.0.0.1:{port}/"), logs)
}
