//! End to end: a node, its gateway, a worker that catches what is pushed to
//! it; then two nodes over one store.

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use axum::routing::post;
use axum::{Json, Router};
use echod_server::store::{MemoryStore, Store};
use echod_server::{gateway, Config, Server};
use resonate_core::ResonateServer;
use serde_json::{json, Value};

/// A worker: whatever is pushed to it, it keeps.
struct Worker {
    url: String,
    inbox: Arc<Mutex<Vec<Value>>>,
}

impl Worker {
    async fn start() -> Self {
        let inbox: Arc<Mutex<Vec<Value>>> = Arc::new(Mutex::new(Vec::new()));
        let sink = Arc::clone(&inbox);
        let app = Router::new().route(
            "/",
            post(move |Json(v): Json<Value>| {
                let sink = Arc::clone(&sink);
                async move {
                    sink.lock().unwrap().push(v);
                    axum::http::StatusCode::OK
                }
            }),
        );
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
        Self { url: format!("http://{addr}/"), inbox }
    }

    /// The first message `pred` accepts, within `within`.
    async fn expect(&self, within: Duration, pred: impl Fn(&Value) -> bool) -> Value {
        let start = Instant::now();
        loop {
            if let Some(m) = self.inbox.lock().unwrap().iter().find(|m| pred(m)).cloned() {
                return m;
            }
            assert!(start.elapsed() < within, "no such message within {within:?}; got {:?}", self.inbox.lock().unwrap());
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    }

    fn count(&self, pred: impl Fn(&Value) -> bool) -> usize {
        self.inbox.lock().unwrap().iter().filter(|m| pred(m)).count()
    }
}

struct Node {
    server: Arc<Server>,
    addr: SocketAddr,
    stop: tokio::sync::watch::Sender<bool>,
}

impl Node {
    async fn start(store: Arc<dyn Store>, id: &str, compact: u32) -> Self {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        drop(listener);
        let mut cfg = Config::memory(&addr.to_string());
        cfg.node_id = Some(id.to_string());
        cfg.url = Some(format!("http://{addr}/"));
        cfg.compact = compact;
        cfg.retry_timeout = 600;
        // Small buckets, so the tests cross bucket boundaries.
        cfg.timer_bucket_ms = 400;
        let server = Server::new(cfg, store);
        server.init(false).await.unwrap();
        let (stop, rx) = tokio::sync::watch::channel(false);
        let (addr, _) = gateway::serve(Arc::clone(&server), &addr.to_string(), rx).await.unwrap();
        Self { server, addr, stop }
    }

    async fn send(&self, kind: &str, data: Value) -> (u16, HashMap<String, String>, Value) {
        let body = json!({ "kind": kind, "head": { "corrId": "c1", "version": "2026-04-01" }, "data": data });
        let resp = reqwest::Client::new().post(format!("http://{}/", self.addr)).json(&body).send().await.unwrap();
        let status = resp.status().as_u16();
        let headers = resp.headers().iter().map(|(k, v)| (k.to_string(), v.to_str().unwrap_or_default().to_string())).collect();
        let v: Value = resp.json().await.unwrap();
        assert_eq!(v["kind"], kind);
        assert_eq!(v["head"]["corrId"], "c1");
        assert_eq!(v["head"]["status"].as_u64().unwrap() as u16, status);
        (status, headers, v["data"].clone())
    }

    async fn stop(self) {
        self.server.stop().await.unwrap();
        let _ = self.stop.send(true);
    }
}

fn now() -> u64 {
    resonate_core::util::system_time_ms() as u64
}

fn is_execute(id: &str) -> impl Fn(&Value) -> bool + '_ {
    move |m| m["kind"] == "execute" && m["data"]["task"]["id"] == id
}

fn is_unblock(id: &str) -> impl Fn(&Value) -> bool + '_ {
    move |m| m["kind"] == "unblock" && m["data"]["promise"]["id"] == id
}

async fn one_node(store: Arc<dyn Store>, compact: u32) {
    let worker = Worker::start().await;
    let node = Node::start(Arc::clone(&store), "n1", compact).await;
    let far = now() + 3_600_000;

    // nothing there
    let (status, headers, _) = node.send("promise.get", json!({ "id": "a:1" })).await;
    assert_eq!(status, 404);
    assert_eq!(headers.get("x-echod-node").map(String::as_str), Some("n1"));

    // a promise with a target is a task, and the task is offered
    let (status, _, data) = node.send("promise.create", json!({ "id": "a:1", "timeoutAt": far, "tags": { "resonate:target": worker.url }, "param": { "data": "hi" } })).await;
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["promise"]["state"], "pending");
    let exec = worker.expect(Duration::from_secs(3), is_execute("a:1")).await;
    let version = exec["data"]["task"]["version"].as_i64().unwrap();
    assert_eq!(exec["head"]["serverUrl"], format!("http://{}/", node.addr));

    // create again: same promise, no second offer
    let (status, _, _) = node.send("promise.create", json!({ "id": "a:1", "timeoutAt": far, "tags": { "resonate:target": worker.url } })).await;
    assert_eq!(status, 200);

    // claim it, read it, finish it
    let (status, _, data) = node.send("task.acquire", json!({ "id": "a:1", "version": version, "pid": "p1", "ttl": 60_000 })).await;
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["task"]["state"], "acquired");
    assert_eq!(data["promise"]["param"]["data"], "hi");
    // acquiring fences: the version the worker holds is the one it was given
    let version = data["task"]["version"].as_i64().unwrap();
    let (status, _, data) = node.send("task.get", json!({ "id": "a:1" })).await;
    assert_eq!(status, 200);
    assert_eq!(data["task"]["pid"], "p1");
    let (status, _, _) = node.send("task.heartbeat", json!({ "pid": "p1", "tasks": [{ "id": "a:1", "version": version }] })).await;
    assert_eq!(status, 200);

    // an awaitable child the task suspends on; only an external promise can be awaited
    let (status, _, _) = node.send("task.fence", json!({ "id": "a:1", "version": version, "action": { "kind": "promise.create", "head": {}, "data": { "id": "a:1.1", "timeoutAt": far, "tags": { "resonate:scope": "global" } } } })).await;
    assert_eq!(status, 200);
    let (status, _, _) = node.send("task.suspend", json!({ "id": "a:1", "version": version, "actions": [{ "kind": "promise.register_callback", "head": {}, "data": { "awaited": "a:1.1", "awaiter": "a:1" } }] })).await;
    assert_eq!(status, 200);
    let (_, _, data) = node.send("task.get", json!({ "id": "a:1" })).await;
    assert_eq!(data["task"]["state"], "suspended");

    // settling the child wakes the task: another offer, at the fenced version
    let offers = worker.count(is_execute("a:1"));
    let (status, _, data) = node.send("promise.settle", json!({ "id": "a:1.1", "state": "resolved", "value": { "data": "child" } })).await;
    assert_eq!(status, 200, "{data}");
    let start = Instant::now();
    while worker.count(is_execute("a:1")) <= offers {
        assert!(start.elapsed() < Duration::from_secs(3), "the task was not re-offered");
        tokio::time::sleep(Duration::from_millis(25)).await;
    }
    let exec = worker.expect(Duration::from_secs(1), |m| is_execute("a:1")(m) && m["data"]["task"]["version"].as_i64().unwrap() == version).await;
    assert_eq!(exec["data"]["task"]["version"], version);
    let (status, _, data) = node.send("task.acquire", json!({ "id": "a:1", "version": version, "pid": "p1", "ttl": 60_000 })).await;
    assert_eq!(status, 200, "{data}");
    let version = data["task"]["version"].as_i64().unwrap();
    let (status, _, data) = node.send("task.fulfill", json!({ "id": "a:1", "version": version, "action": { "kind": "promise.settle", "head": {}, "data": { "id": "a:1", "state": "resolved", "value": { "data": "done" } } } })).await;
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["promise"]["state"], "resolved");
    let (status, _, data) = node.send("task.get", json!({ "id": "a:1" })).await;
    assert_eq!(status, 200);
    assert_eq!(data["task"]["state"], "fulfilled");

    // a listener on a pending promise is told when it settles
    let (status, _, _) = node.send("promise.create", json!({ "id": "b:1", "timeoutAt": far, "tags": { "resonate:scope": "global" } })).await;
    assert_eq!(status, 200);
    let (status, _, _) = node.send("promise.register_listener", json!({ "awaited": "b:1", "address": worker.url })).await;
    assert_eq!(status, 200);
    let (status, _, _) = node.send("promise.settle", json!({ "id": "b:1", "state": "rejected" })).await;
    assert_eq!(status, 200);
    let m = worker.expect(Duration::from_secs(3), is_unblock("b:1")).await;
    assert_eq!(m["data"]["promise"]["state"], "rejected");

    // a deadline fires on its own
    let (status, _, _) = node.send("promise.create", json!({ "id": "c:1", "timeoutAt": now() + 400, "tags": { "resonate:scope": "global" } })).await;
    assert_eq!(status, 200);
    let (status, _, _) = node.send("promise.register_listener", json!({ "awaited": "c:1", "address": worker.url })).await;
    assert_eq!(status, 200);
    let m = worker.expect(Duration::from_secs(4), is_unblock("c:1")).await;
    assert_eq!(m["data"]["promise"]["state"], "rejected_timedout");

    // a sleep, as the SDK creates one: a timer with a target. No task, and the
    // deadline resolves it
    let (status, _, data) = node.send("promise.create", json!({ "id": "c:2", "timeoutAt": now() + 400, "tags": { "resonate:timer": "true", "resonate:target": worker.url } })).await;
    assert_eq!(status, 200, "{data}");
    assert!(data["promise"]["tags"].get("resonate:target").is_none());
    let (status, _, _) = node.send("task.get", json!({ "id": "c:2" })).await;
    assert_eq!(status, 404);
    let (status, _, _) = node.send("promise.register_listener", json!({ "awaited": "c:2", "address": worker.url })).await;
    assert_eq!(status, 200);
    let m = worker.expect(Duration::from_secs(4), is_unblock("c:2")).await;
    assert_eq!(m["data"]["promise"]["state"], "resolved");
    let (status, _, data) = node.send("promise.get", json!({ "id": "c:9" })).await;
    assert_eq!(status, 404);
    assert!(data.is_string(), "an error carries a reason: {data}");

    // an unclaimed task is offered again after the retry timeout
    let (status, _, _) = node.send("promise.create", json!({ "id": "d:1", "timeoutAt": far, "tags": { "resonate:target": worker.url } })).await;
    assert_eq!(status, 200);
    worker.expect(Duration::from_secs(4), |m| is_execute("d:1")(m)).await;
    let start = Instant::now();
    while worker.count(is_execute("d:1")) < 2 {
        assert!(start.elapsed() < Duration::from_secs(4), "no second offer");
        tokio::time::sleep(Duration::from_millis(25)).await;
    }

    // a schedule fires every second
    let (status, _, data) = node
        .send("schedule.create", json!({ "id": "tick", "cron": "* * * * * *", "promiseId": "tick-{{.timestamp}}", "promiseTimeout": 60_000, "promiseTags": { "resonate:target": worker.url } }))
        .await;
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["schedule"]["id"], "tick");
    let m = worker.expect(Duration::from_secs(5), |m| m["kind"] == "execute" && m["data"]["task"]["id"].as_str().unwrap_or_default().starts_with("tick-")).await;
    let fired = m["data"]["task"]["id"].as_str().unwrap().to_string();
    let (status, _, data) = node.send("promise.get", json!({ "id": fired })).await;
    assert_eq!(status, 200);
    assert_eq!(data["promise"]["tags"]["resonate:schedule"], "tick");
    assert_eq!(data["promise"]["tags"]["resonate:origin"], fired);
    let (status, _, data) = node.send("schedule.get", json!({ "id": "tick" })).await;
    assert_eq!(status, 200);
    assert!(data["schedule"]["lastRunAt"].is_i64() || data["schedule"]["lastRunAt"].is_u64(), "{data}");
    let (status, _, _) = node.send("schedule.delete", json!({ "id": "tick" })).await;
    assert_eq!(status, 200);
    let (status, _, _) = node.send("schedule.get", json!({ "id": "tick" })).await;
    assert_eq!(status, 404);

    // what is refused
    let (status, _, _) = node.send("promise.search", json!({})).await;
    assert_eq!(status, 403);
    let (status, _, _) = node.send("debug.tick", json!({})).await;
    assert_eq!(status, 403);
    let (status, _, _) = node.send("promise.frobnicate", json!({})).await;
    assert_eq!(status, 400);
    let (status, _, _) = node.send("promise.create", json!({ "id": "" })).await;
    assert_eq!(status, 400);

    node.stop().await;
}

#[tokio::test]
async fn one_node_rewriting() {
    one_node(Arc::new(MemoryStore::new()), 0).await;
}

#[tokio::test]
async fn one_node_appending() {
    let store = Arc::new(MemoryStore::appendable());
    one_node(Arc::clone(&store) as Arc<dyn Store>, 64).await;
    // the document is a log: more rows than promises
    let (bytes, _) = store.get("wf/a").await.unwrap().unwrap();
    let loaded = echod_server::doc::decode(&bytes).unwrap();
    assert_eq!(loaded.rows.len(), 2);
    assert!(loaded.row_count > 2, "{} rows", loaded.row_count);
}

/// A deadline outlives the node that armed it: a fresh node, with a fresh
/// wheel, loads the buckets at startup and fires it. The deadline sits several
/// buckets past the horizon the new node loads first, so the wheel has to
/// extend as the clock reaches it.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn deadline_survives_a_restart() {
    let memory = Arc::new(MemoryStore::new());
    let store: Arc<dyn Store> = Arc::clone(&memory) as Arc<dyn Store>;
    let worker = Worker::start().await;
    let first = Node::start(Arc::clone(&store), "first", 0).await;
    let (status, _, _) = first.send("promise.create", json!({ "id": "r:1", "timeoutAt": now() + 1_800, "tags": { "resonate:scope": "global" } })).await;
    assert_eq!(status, 200);
    let (status, _, _) = first.send("promise.register_listener", json!({ "awaited": "r:1", "address": worker.url })).await;
    assert_eq!(status, 200);
    first.stop().await;
    let timer_keys = || store_keys(&store).into_iter().filter(|k| k.starts_with("t/")).count();
    assert_eq!(timer_keys(), 1, "the key is in the bucket");

    let listings_before = memory.listings();
    let second = Node::start(Arc::clone(&store), "second", 0).await;
    let m = worker.expect(Duration::from_secs(5), is_unblock("r:1")).await;
    // What the new node listed to get there: the node prefix once at init,
    // the timer prefix and its buckets once at startup, then one bucket per
    // 400 ms crossed. Never a poll.
    let fired_after = Duration::from_millis(1_800);
    let buckets_crossed = (fired_after.as_millis() / 400) as usize + 2;
    let listed = memory.listings() - listings_before;
    assert!(listed <= 1 + 1 + 1 + buckets_crossed + 2, "{listed} listings for one restart and {buckets_crossed} buckets");
    assert_eq!(m["data"]["promise"]["state"], "rejected_timedout");
    let start = Instant::now();
    while timer_keys() > 0 {
        assert!(start.elapsed() < Duration::from_secs(2), "the fired key was not collected");
        tokio::time::sleep(Duration::from_millis(25)).await;
    }
    second.stop().await;
}

fn store_keys(store: &Arc<dyn Store>) -> Vec<String> {
    // The memory store lists everything under the empty prefix.
    futures_lite_block_on(store.list("", usize::MAX)).unwrap()
}

fn futures_lite_block_on<F: std::future::Future>(f: F) -> F::Output {
    tokio::task::block_in_place(|| tokio::runtime::Handle::current().block_on(f))
}

#[tokio::test]
async fn two_nodes() {
    let store: Arc<dyn Store> = Arc::new(MemoryStore::new());
    let worker = Worker::start().await;
    let a = Node::start(Arc::clone(&store), "a", 0).await;
    let b = Node::start(Arc::clone(&store), "b", 0).await;
    let far = now() + 3_600_000;

    // they find each other
    let start = Instant::now();
    while a.server.nodes().members().nodes.len() < 2 || b.server.nodes().members().nodes.len() < 2 {
        assert!(start.elapsed() < Duration::from_secs(3), "nodes never met");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }

    // every origin has one owner, and both nodes agree on it
    let owner = a.server.nodes().owner("x").unwrap().id;
    assert_eq!(owner, b.server.nodes().owner("x").unwrap().id);
    let (own, other) = if owner == "a" { (&a, &b) } else { (&b, &a) };

    // a request to the other node is answered by the owner
    let (status, headers, _) = other.send("promise.create", json!({ "id": "x:1", "timeoutAt": far, "tags": { "resonate:scope": "global" } })).await;
    assert_eq!(status, 200);
    assert_eq!(headers.get("x-echod-node").map(String::as_str), Some(owner.as_str()));
    let (status, headers, _) = own.send("promise.get", json!({ "id": "x:1" })).await;
    assert_eq!(status, 200);
    assert_eq!(headers.get("x-echod-node").map(String::as_str), Some(owner.as_str()));

    // a deadline armed through either node fires once
    let (status, _, _) = other.send("promise.create", json!({ "id": "x:2", "timeoutAt": now() + 400, "tags": { "resonate:scope": "global" } })).await;
    assert_eq!(status, 200);
    let (status, _, _) = own.send("promise.register_listener", json!({ "awaited": "x:2", "address": worker.url })).await;
    assert_eq!(status, 200);
    worker.expect(Duration::from_secs(4), is_unblock("x:2")).await;
    tokio::time::sleep(Duration::from_millis(500)).await;
    assert_eq!(worker.count(is_unblock("x:2")), 1);

    // the owner leaves; the survivor takes its origins and its deadlines
    let (status, _, _) = own.send("promise.create", json!({ "id": "x:3", "timeoutAt": now() + 1_500, "tags": { "resonate:scope": "global" } })).await;
    assert_eq!(status, 200);
    let (status, _, _) = own.send("promise.register_listener", json!({ "awaited": "x:3", "address": worker.url })).await;
    assert_eq!(status, 200);
    let survivor = if owner == "a" {
        a.stop().await;
        b
    } else {
        b.stop().await;
        a
    };
    let start = Instant::now();
    while survivor.server.nodes().members().nodes.len() > 1 {
        assert!(start.elapsed() < Duration::from_secs(3), "the dead node never left");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let m = worker.expect(Duration::from_secs(5), is_unblock("x:3")).await;
    assert_eq!(m["data"]["promise"]["state"], "rejected_timedout");
    let (status, headers, data) = survivor.send("promise.get", json!({ "id": "x:1" })).await;
    assert_eq!(status, 200);
    assert_eq!(headers.get("x-echod-node").map(String::as_str), Some(survivor.server.nodes().id()));
    assert_eq!(data["promise"]["state"], "pending");
    survivor.stop().await;
}
