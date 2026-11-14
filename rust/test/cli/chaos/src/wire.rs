use echod_types::{PromiseCreateReq, PromiseSettleReq, Request, TaskFenceAction};
use serde_json::{json, Value};

fn create(c: &PromiseCreateReq, worker: &str) -> Value {
    let mut tags = echod::codec::map(&c.tags);
    if let Some(target) = tags.get_mut("resonate:target") {
        if target == echod_sim::workload::WORKER {
            *target = worker.to_owned();
        }
    }
    json!({"id": c.id, "timeoutAt": c.timeout_at, "param": echod::codec::value_out(&c.param), "tags": tags})
}

fn settle(s: &PromiseSettleReq) -> Value {
    json!({"id": s.id, "state": s.state, "value": echod::codec::value_out(&s.value)})
}

fn action(kind: &str, data: Value) -> Value {
    json!({"kind": kind, "head": {"corrId": "action", "version": "2026-04-01"}, "data": data})
}

pub fn encode(req: &Request, worker: &str) -> (&'static str, Value) {
    match req {
        Request::PromiseGet(q) => ("promise.get", json!({"id": q.id})),
        Request::PromiseCreate(q) => ("promise.create", create(q, worker)),
        Request::PromiseSettle(q) => ("promise.settle", settle(q)),
        Request::PromiseRegisterCallback(q) => (
            "promise.register_callback",
            json!({"awaited": q.awaited, "awaiter": q.awaiter}),
        ),
        Request::PromiseRegisterListener(q) => (
            "promise.register_listener",
            json!({"awaited": q.awaited, "address": worker}),
        ),
        Request::TaskGet(q) => ("task.get", json!({"id": q.id})),
        Request::TaskCreate(q) => (
            "task.create",
            json!({"pid": q.pid, "ttl": q.ttl, "action": action("promise.create", create(&q.action, worker))}),
        ),
        Request::TaskAcquire(q) => (
            "task.acquire",
            json!({"id": q.id, "version": q.version, "pid": q.pid, "ttl": q.ttl}),
        ),
        Request::TaskRelease(q) => ("task.release", json!({"id": q.id, "version": q.version})),
        Request::TaskFulfill(q) => (
            "task.fulfill",
            json!({"id": q.id, "version": q.version, "action": action("promise.settle", settle(&q.action))}),
        ),
        Request::TaskFence(q) => {
            let nested = match &q.action {
                TaskFenceAction::Create(c) => action("promise.create", create(c, worker)),
                TaskFenceAction::Settle(s) => action("promise.settle", settle(s)),
            };
            (
                "task.fence",
                json!({"id": q.id, "version": q.version, "action": nested}),
            )
        }
        Request::TaskFenceCheck(q) => ("task.fence", json!({"id": q.id, "version": q.version})),
        Request::TaskSuspend(q) => (
            "task.suspend",
            json!({"id": q.id, "version": q.version, "actions": q.actions.iter().map(|a| action("promise.register_callback", json!({"awaited": a.awaited, "awaiter": a.awaiter}))).collect::<Vec<_>>()}),
        ),
        Request::TaskHeartbeat(q) => (
            "task.heartbeat",
            json!({"pid": q.pid, "tasks": q.tasks.iter().map(|t| json!({"id": t.id, "version": t.version})).collect::<Vec<_>>()}),
        ),
        Request::TaskHalt(q) => ("task.halt", json!({"id": q.id})),
        Request::TaskContinue(q) => ("task.continue", json!({"id": q.id})),
        Request::ScheduleGet(q) => ("schedule.get", json!({"id": q.id})),
        Request::ScheduleDelete(q) => ("schedule.delete", json!({"id": q.id})),
        Request::ScheduleCreate(q) => (
            "schedule.create",
            json!({"id": q.id, "cron": q.cron, "promiseId": q.promise_id, "promiseTimeout": q.promise_timeout, "promiseParam": echod::codec::value_out(&q.promise_param), "promiseTags": echod::codec::map(&q.promise_tags)}),
        ),
    }
}

pub fn note(seen: &mut echod_sim::workload::Seen, data: &Value) {
    for task in super::tasks_in(data) {
        if let (Some(id), Some(version)) = (task["id"].as_str(), task["version"].as_u64()) {
            seen.versions.insert(id.into(), version);
        }
    }
    for p in super::promises_in(data) {
        let Some(id) = p["id"].as_str() else { continue };
        let tags = &p["tags"];
        if tags["resonate:target"].is_string() {
            seen.versions.entry(id.into()).or_insert(0);
        }
        if tags["resonate:target"].is_string()
            || tags["resonate:scope"] == "global"
            || tags["resonate:external"] == "true"
            || tags["resonate:timer"] == "true"
        {
            seen.external.insert(id.into());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use echod_sim::{
        rng::Rng,
        workload::{Generator, Seen},
    };

    #[test]
    fn generated_requests_use_the_current_admission_protocol() {
        let generator = Generator {
            origins: 3,
            promises_per_origin: 3,
            schedules: false,
            timeout_ms: 8000,
            ttl_ms: 4000,
        };
        let mut rng = Rng::new(7);
        let mut kinds = std::collections::BTreeSet::new();
        for _ in 0..2000 {
            let req = generator.next(&mut rng, &Seen::default(), 1000);
            let (kind, data) = encode(&req, "http://worker:9100/");
            kinds.insert(kind);
            let envelope = serde_json::from_value(json!({
                "kind": kind, "head": {"corrId": "test", "version": "2026-04-01"}, "data": data
            }))
            .unwrap();
            if let Err(error) = echod::admit::decode(&envelope, 1000, false) {
                panic!("{kind}: {}", serde_json::to_string(&error).unwrap());
            }
        }
        assert_eq!(kinds.len(), 15);
    }

    #[test]
    fn wire_observations_preserve_versions_and_awaitable_tags() {
        let mut seen = Seen::default();
        note(
            &mut seen,
            &json!({"task": {"id": "o1:1", "version": 3},
            "head": {"status": 200}, "data": {"promise": {
                "id": "o1:2", "tags": {"resonate:scope": "global"}
            }}}),
        );
        assert_eq!(seen.versions["o1:1"], 3);
        assert!(seen.external.contains("o1:2"));
        note(
            &mut seen,
            &json!({"head": {"status": 409}, "data": {"task": {"id": "bad", "version": 7}}}),
        );
        assert!(!seen.versions.contains_key("bad"));
    }
}
