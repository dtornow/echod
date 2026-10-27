//! The core driven by hand: a store that is a map, a clock that is a
//! number, no runtime. Every effect the core asks for is performed here,
//! in order, and the answers fed back; what comes out is what a node does.

use std::collections::BTreeMap;

use echod_logic::types::{Effect, Etag, Event, Note, Read, StoreCall, StoreOutcome, SweepOutcome};
use echod_logic::{on_event, Concrete, Config};
use resonate_core::types::{RequestEnvelope, RequestHead, ResponseEnvelope, PROTOCOL_VERSION};
use serde_json::{json, Value};

/// The bucket as a map: every call answered at once, in order.
#[derive(Default)]
struct Bucket {
    objects: BTreeMap<String, (Vec<u8>, u64)>,
}

impl Bucket {
    fn etag(b: &[u8], v: u64) -> Etag {
        Etag(format!("{}-{v}", b.len()))
    }

    fn call(&mut self, c: StoreCall) -> StoreOutcome {
        match c {
            StoreCall::Get { key } => StoreOutcome::Got(self.objects.get(&key).map(|(b, v)| (b.clone(), Self::etag(b, *v)))),
            StoreCall::GetIfNoneMatch { key, etag } => StoreOutcome::Read(match self.objects.get(&key) {
                None => Read::Absent,
                Some((b, v)) if Self::etag(b, *v) == etag => Read::NotModified,
                Some((b, v)) => Read::Body(b.clone(), Self::etag(b, *v)),
            }),
            StoreCall::PutIfMatch { key, body, etag } => match self.objects.get(&key) {
                Some((b, v)) if Self::etag(b, *v) == etag => {
                    let nv = v + 1;
                    let e = Self::etag(&body, nv);
                    self.objects.insert(key, (body, nv));
                    StoreOutcome::Written(e)
                }
                _ => StoreOutcome::Failed(echod_logic::types::StoreError::PreconditionFailed),
            },
            StoreCall::PutIfNoneMatch { key, body } => {
                if self.objects.contains_key(&key) {
                    return StoreOutcome::Failed(echod_logic::types::StoreError::PreconditionFailed);
                }
                let e = Self::etag(&body, 1);
                self.objects.insert(key, (body, 1));
                StoreOutcome::Written(e)
            }
            StoreCall::AppendIfMatch { .. } => StoreOutcome::Failed(echod_logic::types::StoreError::Unavailable("no appends".into())),
            StoreCall::Put { key, body } => {
                let v = self.objects.get(&key).map(|(_, v)| v + 1).unwrap_or(1);
                self.objects.insert(key, (body, v));
                StoreOutcome::Done
            }
            StoreCall::Delete { key } => {
                self.objects.remove(&key);
                StoreOutcome::Done
            }
            StoreCall::List { prefix, max_keys } => StoreOutcome::Listed(self.objects.keys().filter(|k| k.starts_with(&prefix)).take(max_keys).cloned().collect()),
            StoreCall::ListPrefixes { prefix } => {
                let mut out: Vec<String> = Vec::new();
                for k in self.objects.keys().filter(|k| k.starts_with(&prefix)) {
                    if let Some(i) = k[prefix.len()..].find('/') {
                        let p = k[..prefix.len() + i + 1].to_string();
                        if out.last() != Some(&p) {
                            out.push(p);
                        }
                    }
                }
                StoreOutcome::Listed(out)
            }
        }
    }
}

/// A node and its world: the state, the bucket, the clock, and what came
/// out that was not a store call.
struct Harness {
    state: Concrete,
    bucket: Bucket,
    clock: u64,
    replies: Vec<(u64, Result<ResponseEnvelope, resonate_core::Unavailable>)>,
    sent: Vec<String>,
    notes: Vec<Note>,
    wake_after: Option<u64>,
    next_request: u64,
}

impl Harness {
    fn new(id: &str) -> Self {
        let mut cfg = Config::memory(id);
        cfg.timer_bucket_ms = 1_000;
        cfg.heartbeat_ms = 100;
        cfg.node_ttl_ms = 1_000;
        Self { state: Concrete::new(cfg), bucket: Bucket::default(), clock: 1_000_000, replies: Vec::new(), sent: Vec::new(), notes: Vec::new(), wake_after: None, next_request: 1 }
    }

    /// One event in, and every store call it leads to answered, until the
    /// core asks for nothing more of the store.
    fn apply(&mut self, event: Event) {
        let mut pending = on_event(&mut self.state, event);
        while !pending.is_empty() {
            let mut next = Vec::new();
            for e in pending {
                match e {
                    Effect::Store { op, call } => {
                        let outcome = self.bucket.call(call);
                        next.extend(on_event(&mut self.state, Event::Completed { op, outcome, clock: self.clock }));
                    }
                    Effect::Reply { id, response } => self.replies.push((id, response)),
                    Effect::Send { address, message } => self.sent.push(format!("{address} {}", serde_json::to_string(&message).unwrap())),
                    Effect::Wake { after_ms } => self.wake_after = Some(after_ms),
                    Effect::Note(n) => self.notes.push(n),
                }
            }
            pending = next;
        }
    }

    fn request(&mut self, kind: &str, data: Value) -> (u16, Value) {
        let id = self.next_request;
        self.next_request += 1;
        let envelope = RequestEnvelope { kind: kind.to_string(), head: RequestHead { corr_id: format!("c{id}"), version: PROTOCOL_VERSION.to_string(), auth: None, debug_time: None }, data };
        self.apply(Event::Request { id, envelope, clock: self.clock });
        let (rid, r) = self.replies.pop().expect("an answer");
        assert_eq!(rid, id);
        let r = r.expect("served");
        (r.head.status as u16, r.data)
    }

    /// Time passes: the clock moves and the core gets a tick whenever it
    /// asked for one, as the executor's timer would give it.
    fn advance(&mut self, ms: u64) {
        let until = self.clock + ms;
        while self.clock < until {
            let step = self.wake_after.unwrap_or(until - self.clock).min(until - self.clock).max(1);
            self.clock += step;
            self.wake_after = None;
            self.apply(Event::Tick { clock: self.clock });
        }
    }

    fn keys(&self, prefix: &str) -> Vec<String> {
        self.bucket.objects.keys().filter(|k| k.starts_with(prefix)).cloned().collect()
    }
}

#[test]
fn a_promise_is_created_timed_out_and_the_key_collected() {
    let mut h = Harness::new("n1");
    h.apply(Event::Start { clock: h.clock, loops: true });
    // announced; the configuration naming this node is written by the
    // first refresh and read by the next heartbeat
    assert_eq!(h.keys("nodes/"), vec!["nodes/n1".to_string()]);
    assert!(!h.state.acting(), "no configuration read yet");
    h.advance(100);
    assert!(h.state.acting(), "one node, one member, fresh");
    assert_eq!(h.state.membership().members, vec!["n1".to_string()]);
    assert!(h.wake_after.is_some(), "the heartbeat is scheduled");

    // a promise with a deadline: a document, and a key put before it
    let (status, data) = h.request("promise.create", json!({ "id": "a:1", "timeoutAt": h.clock + 500, "tags": { "resonate:scope": "global" } }));
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["promise"]["state"], "pending");
    assert_eq!(h.keys("wf/").len(), 1);
    assert_eq!(h.keys("t/").len(), 1, "one deadline key");
    let (status, data) = h.request("promise.get", json!({ "id": "a:1" }));
    assert_eq!(status, 200);
    assert_eq!(data["promise"]["state"], "pending");
    assert!(h.notes.iter().any(|n| matches!(n, Note::Cache(echod_logic::types::CacheResult::Revalidated))), "the second load revalidated the cache");

    // a listener, then the deadline: the sweep rejects the promise and
    // the listener hears of it
    let (status, _) = h.request("promise.register_listener", json!({ "awaited": "a:1", "address": "http://worker/" }));
    assert_eq!(status, 200);
    h.advance(600);
    let (status, data) = h.request("promise.get", json!({ "id": "a:1" }));
    assert_eq!(status, 200);
    assert_eq!(data["promise"]["state"], "rejected_timedout", "{data}");
    assert!(h.notes.iter().any(|n| matches!(n, Note::Sweep(SweepOutcome::Fired))));
    assert_eq!(h.sent.len(), 1, "one unblock: {:?}", h.sent);
    assert!(h.sent[0].starts_with("http://worker/ "));
    assert!(h.keys("t/").is_empty(), "the fired key was collected");

    // stop: the announcement goes
    h.apply(Event::Stop { clock: h.clock });
    assert!(h.state.stopped());
    assert!(h.keys("nodes/").is_empty());
}

#[test]
fn a_schedule_fires_into_its_origin() {
    let mut h = Harness::new("n1");
    h.apply(Event::Start { clock: h.clock, loops: true });
    h.advance(100);
    let (status, data) = h.request("schedule.create", json!({ "id": "tick", "cron": "* * * * * *", "promiseId": "tick-{{.timestamp}}", "promiseTimeout": 60_000, "promiseTags": { "resonate:target": "http://worker/" } }));
    assert_eq!(status, 200, "{data}");
    assert_eq!(h.keys("sched/").len(), 1);
    assert_eq!(h.keys("t/").len(), 1, "the next run has a key");
    h.advance(1_100);
    assert!(h.notes.iter().any(|n| matches!(n, Note::FireBegin { .. })), "the schedule fired");
    assert!(h.notes.iter().any(|n| matches!(n, Note::AdvanceEnd { committed: true, .. })));
    assert_eq!(h.sent.len(), 1, "the occurrence's task was offered: {:?}", h.sent);
    let (status, data) = h.request("schedule.get", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    assert!(data["schedule"]["lastRunAt"].is_number(), "{data}");
    assert_eq!(h.keys("t/").len(), 2, "the occurrence's deadline and the next run: {:?}", h.keys("t/"));
    let (status, _) = h.request("schedule.delete", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    let (status, _) = h.request("schedule.get", json!({ "id": "tick" }));
    assert_eq!(status, 404);
}

/// A bucket is listed ahead of the clock, and again once the clock has left
/// it: a key another node armed into it in between, for a target this node
/// owns, is found then rather than at the next membership change.
#[test]
fn a_bucket_is_listed_again_once_the_clock_leaves_it() {
    let mut h = Harness::new("n1");
    h.apply(Event::Start { clock: h.clock, loops: true });
    h.advance(100);
    let bucket_ms = 1_000; // the harness's `timer_bucket_ms`
    let current = h.clock - h.clock % bucket_ms;
    let listed = |h: &Harness, b: u64| h.notes.iter().filter(|n| matches!(n, Note::BucketLoaded { bucket, .. } if *bucket == b)).count();
    // the full load reached the next bucket; nothing more while the clock
    // stays in this one
    h.advance(bucket_ms / 2);
    assert_eq!(listed(&h, current), 0);
    // the clock leaves the bucket: it is listed once more, and the horizon
    // moves on by one
    h.advance(bucket_ms / 2 + 10);
    assert_eq!(listed(&h, current), 1, "the bucket just closed is listed again");
    assert_eq!(listed(&h, current + 2 * bucket_ms), 1, "and the horizon moved on");
}

/// A schedule deleted and created again under the same id fires again: the
/// new document's next run gets a key of its own, whatever key the old one
/// left behind.
#[test]
fn a_schedule_recreated_after_its_delete_fires_again() {
    let mut h = Harness::new("n1");
    h.apply(Event::Start { clock: h.clock, loops: true });
    h.advance(100);
    let (status, _) = h.request("schedule.create", json!({ "id": "tick", "cron": "*/2 * * * * *", "promiseId": "tick-{{.timestamp}}", "promiseTimeout": 60_000, "promiseTags": { "resonate:target": "http://worker/" } }));
    assert_eq!(status, 200);
    let (status, _) = h.request("schedule.delete", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    h.advance(300);
    let fired = h.notes.iter().filter(|n| matches!(n, Note::FireBegin { .. })).count();
    assert_eq!(fired, 0, "a deleted schedule does not fire");
    let (status, data) = h.request("schedule.create", json!({ "id": "tick", "cron": "*/2 * * * * *", "promiseId": "tock-{{.timestamp}}", "promiseTimeout": 60_000, "promiseTags": { "resonate:target": "http://worker/" } }));
    assert_eq!(status, 200, "{data}");
    let next = data["schedule"]["nextRunAt"].as_u64().unwrap();
    h.advance(next - h.clock + 100);
    h.advance(2_100);
    assert!(h.notes.iter().any(|n| matches!(n, Note::FireBegin { .. })), "the recreated schedule fired; keys {:?}", h.keys("t/"));
    let (status, data) = h.request("schedule.get", json!({ "id": "tick" }));
    assert_eq!(status, 200);
    assert!(data["schedule"]["lastRunAt"].is_number(), "{data}");
}

#[test]
fn the_same_events_give_the_same_effects() {
    let run = || {
        let mut h = Harness::new("n1");
        h.apply(Event::Start { clock: h.clock, loops: true });
        h.advance(100);
        h.request("promise.create", json!({ "id": "a:1", "timeoutAt": h.clock + 500, "tags": { "resonate:scope": "global" } }));
        h.advance(600);
        h.bucket.objects.keys().cloned().collect::<Vec<_>>()
    };
    assert_eq!(run(), run());
}

#[test]
fn the_debug_operations_own_the_clock() {
    let mut h = Harness::new("n1");
    h.state = Concrete::new({
        let mut cfg = Config::memory("n1");
        cfg.debug = true;
        cfg
    });
    h.apply(Event::Start { clock: h.clock, loops: false });
    let far = h.clock + 10_000;
    let (status, _) = h.request("promise.create", json!({ "id": "a:1", "timeoutAt": far, "tags": { "resonate:scope": "global" } }));
    assert_eq!(status, 200);
    let (status, _) = h.request("promise.register_listener", json!({ "awaited": "a:1", "address": "http://worker/" }));
    assert_eq!(status, 200);

    // the snapshot: the promise, its deadline, its listener
    let (status, snap) = h.request("debug.snap", json!({}));
    assert_eq!(status, 200, "{snap}");
    assert_eq!(snap["promises"].as_array().map(Vec::len), Some(1));
    assert_eq!(snap["promiseTimeouts"][0]["timeout"].as_u64(), Some(far));
    assert_eq!(snap["listeners"][0]["id"], "a:1");
    assert_eq!(snap["tasks"].as_array().map(Vec::len), Some(0));

    // the tick: time moves, the sweep runs, the listener hears
    let (status, data) = h.request("debug.tick", json!({ "time": far + 1 }));
    assert_eq!(status, 200, "{data}");
    let (_, snap) = h.request("debug.snap", json!({}));
    assert_eq!(snap["promises"][0]["state"], "rejected_timedout", "{snap}");
    assert!(snap["promiseTimeouts"].as_array().is_some_and(Vec::is_empty));
    assert_eq!(h.sent.len(), 1, "{:?}", h.sent);

    // the reset: nothing left
    let (status, _) = h.request("debug.reset", json!({}));
    assert_eq!(status, 200);
    assert!(h.keys("wf/").is_empty());
    let (status, _) = h.request("promise.get", json!({ "id": "a:1" }));
    assert_eq!(status, 404);
    let (_, snap) = h.request("debug.snap", json!({}));
    assert!(snap["promises"].as_array().is_some_and(Vec::is_empty));
}

/// A fence whose create targets another origin: the create commits first, on
/// its own document, then the fence's check on the task's. A stale fence
/// still leaves the promise created, and answers its 409; a settle in
/// another origin is refused outright.
#[test]
fn a_detached_create_lands_before_the_fence_is_checked() {
    let mut h = Harness::new("n1");
    h.apply(Event::Start { clock: h.clock, loops: true });
    h.advance(100);
    let far = h.clock + 100_000;
    let (status, _) = h.request("promise.create", json!({ "id": "a:t", "timeoutAt": far, "tags": { "resonate:target": "poll://w" } }));
    assert_eq!(status, 200);
    let (status, data) = h.request("task.acquire", json!({ "id": "a:t", "version": 0, "pid": "w", "ttl": 60_000 }));
    assert_eq!(status, 200, "{data}");
    let create = |id: &str| json!({ "kind": "promise.create", "head": {}, "data": { "id": id, "timeoutAt": far, "tags": {} } });

    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 9, "action": create("d:x") }));
    assert_eq!(status, 409, "{data}");
    assert_eq!(data, json!("Version mismatch"));
    let (status, data) = h.request("promise.get", json!({ "id": "d:x" }));
    assert_eq!(status, 200, "a stale detached create still lands: {data}");
    assert_eq!(data["promise"]["state"], "pending");

    let (status, data) = h.request("task.fence", json!({ "id": "a:ghost", "version": 0, "action": create("d:y") }));
    assert_eq!(status, 404, "{data}");
    let (status, _) = h.request("promise.get", json!({ "id": "d:y" }));
    assert_eq!(status, 200, "a detached create from a missing task lands too");

    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 1, "action": create("d:z") }));
    assert_eq!(status, 200, "{data}");
    assert_eq!(data["action"]["head"]["status"], 200);
    assert_eq!(data["action"]["data"]["promise"]["id"], "d:z");
    assert_eq!(data["preload"], json!([]));
    assert_eq!(h.keys("wf/").len(), 2, "two origins' documents: {:?}", h.keys("wf/"));

    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 9, "action": create("a:n") }));
    assert_eq!(status, 409, "{data}");
    let (status, _) = h.request("promise.get", json!({ "id": "a:n" }));
    assert_eq!(status, 404, "a same-origin stale fence creates nothing");

    let settle = json!({ "kind": "promise.settle", "head": {}, "data": { "id": "d:z", "state": "resolved", "value": {} } });
    let (status, data) = h.request("task.fence", json!({ "id": "a:t", "version": 1, "action": settle }));
    assert_eq!(status, 400, "{data}");
    assert_eq!(data, json!("Action must belong to the task's origin"));
}
