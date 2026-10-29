//! Local conversion between `echod-abstract` and the JSON protocol.
//!
//! This is deliberately owned by the simulator.  The oracle vocabulary is
//! the workspace Abstract machine's; no differential-test or Accordant wire
//! module is imported.

use std::collections::BTreeMap;

use echod_abstract::{
    dup_tags, ExternalAction, Ident, PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq,
    PromiseSettleReq, PromiseState, Response, Schedule, Tag, Tags, TaskFenceAction, TaskRecord,
    Text, Value as AValue,
};
use serde_json::{json, Value};

pub fn text(s: &str) -> Text {
    Text {
        chars: s.chars().collect(),
    }
}

pub fn text_string(s: &Text) -> String {
    s.chars.iter().collect()
}

/// Abstract identifiers split at the first colon, like the refinement map.
pub fn ident(s: &str) -> Ident {
    match s.split_once(':') {
        Some((origin, suffix)) => Ident {
            origin: text(origin),
            suffix: text(suffix),
        },
        None => Ident {
            origin: text(s),
            suffix: Text::empty(),
        },
    }
}

pub fn ident_string(id: &Ident) -> String {
    let origin = text_string(&id.origin);
    let suffix = text_string(&id.suffix);
    if suffix.is_empty() {
        origin
    } else {
        format!("{origin}:{suffix}")
    }
}

fn tags_json(tags: &Tags) -> Value {
    let mut out = serde_json::Map::new();
    for tag in tags {
        out.insert(
            text_string(&tag.key),
            Value::String(text_string(&tag.value)),
        );
    }
    Value::Object(out)
}

fn value_json(value: &AValue) -> Value {
    let mut out = serde_json::Map::new();
    if !value.headers.is_empty() {
        out.insert("headers".into(), tags_json(&value.headers));
    }
    if let Some(data) = &value.data {
        out.insert("data".into(), Value::String(text_string(data)));
    }
    Value::Object(out)
}

fn create_json(req: &PromiseCreateReq) -> Value {
    json!({
        "id": ident_string(&req.id),
        "timeoutAt": req.timeout_at,
        "param": value_json(&req.param),
        "tags": tags_json(&req.tags),
    })
}

fn settle_json(req: &PromiseSettleReq) -> Value {
    json!({
        "id": ident_string(&req.id),
        "state": promise_state_name(req.state),
        "value": value_json(&req.value),
    })
}

/// An Abstract request as the server protocol carries it.
pub fn encode(req: &ExternalAction) -> (&'static str, Value) {
    match req {
        ExternalAction::PromiseGet(q) => ("promise.get", json!({ "id": ident_string(&q.id) })),
        ExternalAction::PromiseCreate(q) => ("promise.create", create_json(q)),
        ExternalAction::PromiseSettle(q) => ("promise.settle", settle_json(q)),
        ExternalAction::PromiseRegisterCallback(q) => (
            "promise.register_callback",
            json!({
                "awaited": ident_string(&q.awaited), "awaiter": ident_string(&q.awaiter),
            }),
        ),
        ExternalAction::PromiseRegisterListener(q) => (
            "promise.register_listener",
            json!({
                "awaited": ident_string(&q.awaited), "address": text_string(&q.address),
            }),
        ),
        ExternalAction::PromiseSearch(_) => ("promise.search", json!({})),
        ExternalAction::ScheduleGet(q) => ("schedule.get", json!({ "id": ident_string(&q.id) })),
        ExternalAction::ScheduleCreate(q) => (
            "schedule.create",
            json!({
                "id": ident_string(&q.id),
                "cron": text_string(&q.cron),
                "promiseId": ident_string(&q.promise_id),
                "promiseTimeout": q.promise_timeout,
                "promiseParam": value_json(&q.promise_param),
                "promiseTags": tags_json(&q.promise_tags),
            }),
        ),
        ExternalAction::ScheduleDelete(q) => {
            ("schedule.delete", json!({ "id": ident_string(&q.id) }))
        }
        ExternalAction::ScheduleSearch(_) => ("schedule.search", json!({})),
        ExternalAction::TaskGet(q) => ("task.get", json!({ "id": ident_string(&q.id) })),
        ExternalAction::TaskCreate(q) => (
            "task.create",
            json!({
                "pid": text_string(&q.pid),
                "ttl": q.ttl,
                "action": { "kind": "promise.create", "head": {}, "data": create_json(&q.action) },
            }),
        ),
        ExternalAction::TaskAcquire(q) => (
            "task.acquire",
            json!({
                "id": ident_string(&q.id), "version": q.version,
                "pid": text_string(&q.pid), "ttl": q.ttl,
            }),
        ),
        ExternalAction::TaskFence(q) => {
            let action = match &q.action {
                TaskFenceAction::Create(a) => json!({
                    "kind": "promise.create", "head": {}, "data": create_json(a),
                }),
                TaskFenceAction::Settle(a) => json!({
                    "kind": "promise.settle", "head": {}, "data": settle_json(a),
                }),
            };
            (
                "task.fence",
                json!({
                    "id": ident_string(&q.id), "version": q.version, "action": action,
                }),
            )
        }
        ExternalAction::TaskHeartbeat(q) => (
            "task.heartbeat",
            json!({
                "pid": text_string(&q.pid),
                "tasks": q.tasks.iter().map(|t| json!({
                    "id": ident_string(&t.id), "version": t.version,
                })).collect::<Vec<_>>(),
            }),
        ),
        ExternalAction::TaskSuspend(q) => (
            "task.suspend",
            json!({
                "id": ident_string(&q.id),
                "version": q.version,
                "actions": q.actions.iter().map(|a| json!({
                    "kind": "promise.register_callback",
                    "head": {},
                    "data": {
                        "awaited": ident_string(&a.awaited),
                        "awaiter": ident_string(&a.awaiter),
                    },
                })).collect::<Vec<_>>(),
            }),
        ),
        ExternalAction::TaskFulfill(q) => (
            "task.fulfill",
            json!({
                "id": ident_string(&q.id),
                "version": q.version,
                "action": { "kind": "promise.settle", "head": {}, "data": settle_json(&q.action) },
            }),
        ),
        ExternalAction::TaskRelease(q) => (
            "task.release",
            json!({
                "id": ident_string(&q.id), "version": q.version,
            }),
        ),
        ExternalAction::TaskHalt(q) => ("task.halt", json!({ "id": ident_string(&q.id) })),
        ExternalAction::TaskContinue(q) => ("task.continue", json!({ "id": ident_string(&q.id) })),
        ExternalAction::TaskSearch(_) => ("task.search", json!({})),
    }
}

pub fn action_kind(req: &ExternalAction) -> &'static str {
    encode(req).0
}

fn promise_state_name(state: PromiseState) -> &'static str {
    match state {
        PromiseState::Pending => "pending",
        PromiseState::Resolved => "resolved",
        PromiseState::Rejected => "rejected",
        PromiseState::RejectedCanceled => "rejected_canceled",
        PromiseState::RejectedTimedout => "rejected_timedout",
    }
}

fn parse_promise_state(s: &str) -> Option<PromiseState> {
    Some(match s {
        "pending" => PromiseState::Pending,
        "resolved" => PromiseState::Resolved,
        "rejected" => PromiseState::Rejected,
        "rejected_canceled" => PromiseState::RejectedCanceled,
        "rejected_timedout" => PromiseState::RejectedTimedout,
        _ => return None,
    })
}

fn parse_tags(value: &Value) -> Tags {
    value.as_object().map_or_else(Vec::new, |map| {
        map.iter()
            .filter_map(|(key, value)| {
                value.as_str().map(|value| Tag {
                    key: text(key),
                    value: text(value),
                })
            })
            .collect()
    })
}

fn parse_value(value: &Value) -> AValue {
    AValue {
        headers: parse_tags(&value["headers"]),
        data: value["data"].as_str().map(text),
    }
}

pub fn promise_record_from_json(value: &Value) -> Option<PromiseRecord> {
    Some(PromiseRecord {
        id: ident(value["id"].as_str()?),
        state: parse_promise_state(value["state"].as_str()?)?,
        param: parse_value(&value["param"]),
        value: parse_value(&value["value"]),
        tags: parse_tags(&value["tags"]),
        timeout_at: value["timeoutAt"].as_u64()?,
        created_at: value["createdAt"].as_u64()?,
        settled_at: value["settledAt"].as_u64(),
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PromiseView {
    pub id: String,
    pub state: String,
    pub param: Option<String>,
    pub value: Option<String>,
    pub tags: BTreeMap<String, String>,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaskView {
    pub id: String,
    pub state: String,
    pub version: u64,
    pub resumes: u64,
    pub ttl: Option<u64>,
    pub pid: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScheduleView {
    pub id: String,
    pub cron: String,
    pub promise_id: String,
    pub promise_timeout: u64,
    pub promise_param: Option<String>,
    pub promise_tags: BTreeMap<String, String>,
    pub next_run_at: u64,
    pub last_run_at: Option<u64>,
    pub created_at: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResponseView {
    pub status: u16,
    pub promise: Option<PromiseView>,
    pub task: Option<TaskView>,
    pub schedule: Option<ScheduleView>,
}

fn tag_view(tags: &Tags) -> BTreeMap<String, String> {
    tags.iter()
        .map(|t| (text_string(&t.key), text_string(&t.value)))
        .collect()
}

fn promise_view(p: &PromiseRecord) -> PromiseView {
    PromiseView {
        id: ident_string(&p.id),
        state: promise_state_name(p.state).into(),
        param: p.param.data.as_ref().map(text_string),
        value: p.value.data.as_ref().map(text_string),
        tags: tag_view(&p.tags),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

fn task_state_name(state: echod_abstract::TaskState) -> &'static str {
    match state {
        echod_abstract::TaskState::Pending => "pending",
        echod_abstract::TaskState::Acquired => "acquired",
        echod_abstract::TaskState::Suspended => "suspended",
        echod_abstract::TaskState::Halted => "halted",
        echod_abstract::TaskState::Fulfilled => "fulfilled",
    }
}

fn task_view(t: &TaskRecord) -> TaskView {
    TaskView {
        id: ident_string(&t.id),
        state: task_state_name(t.state).into(),
        version: t.version,
        resumes: t.resumes,
        ttl: t.ttl,
        pid: t.pid.as_ref().map(text_string),
    }
}

fn schedule_view(s: &Schedule) -> ScheduleView {
    ScheduleView {
        id: ident_string(&s.id),
        cron: text_string(&s.cron),
        promise_id: ident_string(&s.promise_id),
        promise_timeout: s.promise_timeout,
        promise_param: s.promise_param.data.as_ref().map(text_string),
        promise_tags: tag_view(&s.promise_tags),
        next_run_at: s.next_run_at,
        last_run_at: s.last_run_at,
        created_at: s.created_at,
    }
}

fn response(
    status: u16,
    promise: Option<&PromiseRecord>,
    task: Option<&TaskRecord>,
    schedule: Option<&Schedule>,
) -> ResponseView {
    ResponseView {
        status,
        promise: promise.map(promise_view),
        task: task.map(task_view),
        schedule: schedule.map(schedule_view),
    }
}

/// Normalize an Abstract oracle response to the protocol-observable fields.
pub fn model_response_view(value: &Response) -> ResponseView {
    match value {
        Response::PromiseGet(r)
        | Response::PromiseCreate(r)
        | Response::PromiseSettle(r)
        | Response::PromiseRegisterCallback(r)
        | Response::PromiseRegisterListener(r) => {
            response(r.status, r.promise.as_ref(), None, None)
        }
        Response::PromiseSearch(r) => response(r.status, None, None, None),
        Response::ScheduleGet(r) | Response::ScheduleCreate(r) => {
            response(r.status, None, None, r.schedule.as_ref())
        }
        Response::ScheduleDelete(r) => response(r.status, None, None, None),
        Response::ScheduleSearch(r) => response(r.status, None, None, None),
        Response::TaskGet(r) => response(r.status, None, r.task.as_ref(), None),
        Response::TaskCreate(r) | Response::TaskAcquire(r) => {
            response(r.status, r.promise.as_ref(), r.task.as_ref(), None)
        }
        Response::TaskFence(r) => match &r.action {
            Some(echod_abstract::TaskFenceInnerRes::Create(inner))
            | Some(echod_abstract::TaskFenceInnerRes::Settle(inner)) => {
                response(inner.status, inner.promise.as_ref(), None, None)
            }
            None => response(r.status, None, None, None),
        },
        Response::TaskHeartbeat(r)
        | Response::TaskRelease(r)
        | Response::TaskHalt(r)
        | Response::TaskContinue(r) => response(r.status, None, None, None),
        Response::TaskSuspend(r) => response(r.status, None, None, None),
        Response::TaskFulfill(r) => response(r.status, r.promise.as_ref(), None, None),
        Response::TaskSearch(r) => response(r.status, None, None, None),
        Response::Silent => response(0, None, None, None),
    }
}

fn promise_view_json(value: &Value) -> Option<PromiseView> {
    let p = promise_record_from_json(value)?;
    Some(promise_view(&p))
}

fn task_view_json(value: &Value) -> Option<TaskView> {
    Some(TaskView {
        id: value["id"].as_str()?.to_string(),
        state: value["state"].as_str()?.to_string(),
        version: value["version"].as_u64()?,
        resumes: value["resumes"].as_u64().unwrap_or(0),
        ttl: value["ttl"].as_u64(),
        pid: value["pid"].as_str().map(str::to_string),
    })
}

fn schedule_view_json(value: &Value) -> Option<ScheduleView> {
    Some(ScheduleView {
        id: value["id"].as_str()?.to_string(),
        cron: value["cron"].as_str()?.to_string(),
        promise_id: value["promiseId"].as_str()?.to_string(),
        promise_timeout: value["promiseTimeout"].as_u64()?,
        promise_param: value["promiseParam"]["data"].as_str().map(str::to_string),
        promise_tags: value["promiseTags"]
            .as_object()
            .map_or_else(BTreeMap::new, |m| {
                m.iter()
                    .filter_map(|(k, v)| v.as_str().map(|v| (k.clone(), v.to_string())))
                    .collect()
            }),
        next_run_at: value["nextRunAt"].as_u64()?,
        last_run_at: value["lastRunAt"].as_u64(),
        created_at: value["createdAt"].as_u64()?,
    })
}

/// Normalize one concrete protocol answer exactly as the oracle is observed.
pub fn decode_response(kind: &str, status: u16, data: &Value) -> ResponseView {
    if status != 200 {
        return response(status, None, None, None);
    }
    let (status, body) = if kind == "task.fence" {
        let inner = data["action"]["head"]["status"]
            .as_u64()
            .unwrap_or(status as u64) as u16;
        (inner, &data["action"]["data"])
    } else {
        (status, data)
    };
    if status != 200 {
        return response(status, None, None, None);
    }
    ResponseView {
        status,
        promise: promise_view_json(&body["promise"]),
        task: task_view_json(&body["task"]),
        schedule: schedule_view_json(&body["schedule"]),
    }
}

/// External actions are intentionally model values; this is their local
/// executable duplication routine for branching search.
pub fn clone_action(a: &ExternalAction) -> ExternalAction {
    match a {
        ExternalAction::PromiseGet(q) => {
            ExternalAction::PromiseGet(echod_abstract::PromiseGetReq { id: q.id.dup() })
        }
        ExternalAction::PromiseCreate(q) => ExternalAction::PromiseCreate(clone_create(q)),
        ExternalAction::PromiseSettle(q) => ExternalAction::PromiseSettle(clone_settle(q)),
        ExternalAction::PromiseRegisterCallback(q) => {
            ExternalAction::PromiseRegisterCallback(clone_callback(q))
        }
        ExternalAction::PromiseRegisterListener(q) => {
            ExternalAction::PromiseRegisterListener(echod_abstract::PromiseRegisterListenerReq {
                awaited: q.awaited.dup(),
                address: q.address.dup(),
            })
        }
        ExternalAction::PromiseSearch(q) => {
            ExternalAction::PromiseSearch(echod_abstract::PromiseSearchReq {
                state: q.state,
                tags: dup_tags(&q.tags),
                limit: q.limit,
                cursor: q.cursor.as_ref().map(Text::dup),
            })
        }
        ExternalAction::ScheduleGet(q) => {
            ExternalAction::ScheduleGet(echod_abstract::ScheduleGetReq { id: q.id.dup() })
        }
        ExternalAction::ScheduleCreate(q) => {
            ExternalAction::ScheduleCreate(echod_abstract::ScheduleCreateReq {
                id: q.id.dup(),
                cron: q.cron.dup(),
                promise_id: q.promise_id.dup(),
                promise_timeout: q.promise_timeout,
                promise_param: q.promise_param.dup(),
                promise_tags: dup_tags(&q.promise_tags),
                next_run_at: q.next_run_at,
            })
        }
        ExternalAction::ScheduleDelete(q) => {
            ExternalAction::ScheduleDelete(echod_abstract::ScheduleDeleteReq { id: q.id.dup() })
        }
        ExternalAction::ScheduleSearch(q) => {
            ExternalAction::ScheduleSearch(echod_abstract::ScheduleSearchReq {
                limit: q.limit,
                cursor: q.cursor.as_ref().map(Text::dup),
            })
        }
        ExternalAction::TaskGet(q) => {
            ExternalAction::TaskGet(echod_abstract::TaskGetReq { id: q.id.dup() })
        }
        ExternalAction::TaskCreate(q) => {
            ExternalAction::TaskCreate(echod_abstract::TaskCreateReq {
                pid: q.pid.dup(),
                ttl: q.ttl,
                action: clone_create(&q.action),
            })
        }
        ExternalAction::TaskAcquire(q) => {
            ExternalAction::TaskAcquire(echod_abstract::TaskAcquireReq {
                id: q.id.dup(),
                version: q.version,
                pid: q.pid.dup(),
                ttl: q.ttl,
            })
        }
        ExternalAction::TaskFence(q) => ExternalAction::TaskFence(echod_abstract::TaskFenceReq {
            id: q.id.dup(),
            version: q.version,
            action: match &q.action {
                TaskFenceAction::Create(x) => TaskFenceAction::Create(clone_create(x)),
                TaskFenceAction::Settle(x) => TaskFenceAction::Settle(clone_settle(x)),
            },
        }),
        ExternalAction::TaskHeartbeat(q) => {
            ExternalAction::TaskHeartbeat(echod_abstract::TaskHeartbeatReq {
                pid: q.pid.dup(),
                tasks: q
                    .tasks
                    .iter()
                    .map(|t| echod_abstract::TaskRef {
                        id: t.id.dup(),
                        version: t.version,
                    })
                    .collect(),
            })
        }
        ExternalAction::TaskSuspend(q) => {
            ExternalAction::TaskSuspend(echod_abstract::TaskSuspendReq {
                id: q.id.dup(),
                version: q.version,
                actions: q.actions.iter().map(clone_callback).collect(),
            })
        }
        ExternalAction::TaskFulfill(q) => {
            ExternalAction::TaskFulfill(echod_abstract::TaskFulfillReq {
                id: q.id.dup(),
                version: q.version,
                action: clone_settle(&q.action),
            })
        }
        ExternalAction::TaskRelease(q) => {
            ExternalAction::TaskRelease(echod_abstract::TaskReleaseReq {
                id: q.id.dup(),
                version: q.version,
            })
        }
        ExternalAction::TaskHalt(q) => {
            ExternalAction::TaskHalt(echod_abstract::TaskHaltReq { id: q.id.dup() })
        }
        ExternalAction::TaskContinue(q) => {
            ExternalAction::TaskContinue(echod_abstract::TaskContinueReq { id: q.id.dup() })
        }
        ExternalAction::TaskSearch(q) => {
            ExternalAction::TaskSearch(echod_abstract::TaskSearchReq {
                state: q.state,
                limit: q.limit,
                cursor: q.cursor.as_ref().map(Text::dup),
            })
        }
    }
}

fn clone_create(q: &PromiseCreateReq) -> PromiseCreateReq {
    PromiseCreateReq {
        id: q.id.dup(),
        timeout_at: q.timeout_at,
        param: q.param.dup(),
        tags: dup_tags(&q.tags),
    }
}

fn clone_settle(q: &PromiseSettleReq) -> PromiseSettleReq {
    PromiseSettleReq {
        id: q.id.dup(),
        state: q.state,
        value: q.value.dup(),
    }
}

fn clone_callback(q: &PromiseRegisterCallbackReq) -> PromiseRegisterCallbackReq {
    PromiseRegisterCallbackReq {
        awaited: q.awaited.dup(),
        awaiter: q.awaiter.dup(),
    }
}
