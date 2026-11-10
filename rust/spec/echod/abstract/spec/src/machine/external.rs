//! Mathematical request transitions.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use echod_types::*;
use rover_spec::rover::comm::Time;
use super::*;
use super::super::trusted::*;
use super::super::view::*;

verus! {
// ---------------------------------------------------------------------------
// Requests, as a specification
// ---------------------------------------------------------------------------

#[allow(dead_code)]
pub enum SpecHeld {
    Ok(TaskV),
    Missing,
    Stale,
}

pub open spec fn spec_held(s: StoreV, id: Seq<char>, version: u64, now: Time) -> SpecHeld {
    if !s.tasks.contains_key(id) {
        SpecHeld::Missing
    } else {
        let t = s.tasks[id];
        let seen = if s.promises.contains_key(id) {
            spec_project_task(t, spec_project_promise(s.promises[id], now)).state
        } else {
            t.state
        };
        let live = s.promises.contains_key(id)
            && spec_project_promise(s.promises[id], now).state == PromiseState::Pending;
        if seen != TaskState::Acquired || !live || t.version != version {
            SpecHeld::Stale
        } else {
            SpecHeld::Ok(t)
        }
    }
}

pub open spec fn spec_promise_create(req: PromiseCreateReq, s: StoreV, now: Time) -> Seq<OutV> {
    if spec_is_timer(req.tags) && spec_has_target(req.tags) {
        spec_out(spec_promise_res(400, None), s)
    } else if s.promises.contains_key(req.id@) {
        let seen = spec_project_promise(s.promises[req.id@], now);
        spec_out(spec_promise_res(200, Some(spec_promise_record(req.id, seen))), s)
    } else {
        let (p, task) = spec_new_object(req.timeout_at, now, now, req.param, req.tags, spec_has_target(req.tags));
        let rec = spec_promise_record(req.id, p);
        let promises = s.promises.insert(req.id@, p);
        let tasks = match task {
            Some(t) => s.tasks.insert(req.id@, t),
            None => s.tasks,
        };
        spec_out(spec_promise_res(200, Some(rec)), StoreV { promises, tasks, ..s })
    }
}

pub open spec fn spec_promise_settle(req: PromiseSettleReq, s: StoreV, now: Time) -> Seq<OutV> {
    if !req.state.spec_settable() {
        spec_out(spec_promise_res(400, None), s)
    } else if !s.promises.contains_key(req.id@) {
        spec_out(spec_promise_res(404, None), s)
    } else {
        let p = spec_project_promise(s.promises[req.id@], now);
        if p.state != PromiseState::Pending {
            spec_out(spec_promise_res(200, Some(spec_promise_record(req.id, p))), s)
        } else {
            let n = spec_settle(s, req.id@, req.state, req.value, now);
            let res = if n.promises.contains_key(req.id@) {
                spec_promise_res(200, Some(spec_promise_record(req.id, n.promises[req.id@])))
            } else {
                spec_promise_res(500, None)
            };
            spec_out(res, n)
        }
    }
}

pub open spec fn spec_task_create(pid: String, ttl: Time, req: PromiseCreateReq, s: StoreV, now: Time) -> Seq<OutV> {
    if !spec_has_target(req.tags) || spec_is_timer(req.tags) {
        spec_out(spec_claim_res(400, None, None), s)
    } else if s.promises.contains_key(req.id@) {
        let p = s.promises[req.id@];
        if !spec_has_target(p.tags) {
            spec_out(spec_claim_res(422, None, None), s)
        } else if !s.tasks.contains_key(req.id@) {
            spec_out(spec_claim_res(409, None, None), s)
        } else {
            let seen_p = spec_project_promise(p, now);
            let stored = s.tasks[req.id@];
            let seen_t = spec_project_task(stored, seen_p);
            match seen_t.state {
                TaskState::Fulfilled => spec_out(
                    spec_claim_res(200, Some(spec_task_record(req.id, seen_t)), Some(spec_promise_record(req.id, seen_p))),
                    s,
                ),
                TaskState::Pending => {
                    let u = spec_acquire(stored, sat_add(stored.version, 1), pid@, ttl, now);
                    let n = StoreV { tasks: s.tasks.insert(req.id@, u), ..s };
                    spec_out(
                        spec_claim_res(200, Some(spec_task_record(req.id, u)), Some(spec_promise_record(req.id, seen_p))),
                        n,
                    )
                },
                _ => spec_out(spec_claim_res(409, None, None), s),
            }
        }
    } else {
        let live = req.timeout_at > now;
        let p = PromiseV {
            state: if live { PromiseState::Pending } else { PromiseState::RejectedTimedout },
            value: spec_empty_value(),
            param: req.param,
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: req.tags,
            callbacks: Set::empty(),
            listeners: Set::empty(),
        };
        let born = TaskV {
            state: TaskState::Fulfilled,
            version: 0,
            pid: None,
            ttl: None,
            acquired_at: 0,
            retry_timeout_at: None,
            resumes: Seq::empty(),
        };
        let t = if live { spec_acquire(born, 1, pid@, ttl, now) } else { born };
        let n = StoreV {
            promises: s.promises.insert(req.id@, p),
            tasks: s.tasks.insert(req.id@, t),
            ..s
        };
        spec_out(
            spec_claim_res(200, Some(spec_task_record(req.id, t)), Some(spec_promise_record(req.id, p))),
            n,
        )
    }
}

pub open spec fn spec_awaited(actions: Seq<PromiseRegisterCallbackReq>) -> Seq<Seq<char>> {
    actions.map_values(|a: PromiseRegisterCallbackReq| a.awaited@)
}

/// `spec_refs_one_origin` from `j` is the pointwise statement.
pub proof fn lemma_refs_one_origin(refs: Seq<TaskRef>, j: int)
    requires
        1 <= j,
    ensures
        spec_refs_one_origin(refs, j) <==> (forall|k: int| j <= k < refs.len() ==> origin(#[trigger] refs[k].id@) == origin(refs[0].id@)),
    decreases refs.len() - j,
{
    if j < refs.len() {
        lemma_refs_one_origin(refs, j + 1);
    }
}

pub open spec fn spec_callbacks(
    promises: Map<Seq<char>, PromiseV>,
    ids: Seq<Seq<char>>,
    awaiter: Seq<char>,
    i: int,
) -> Map<Seq<char>, PromiseV>
    decreases ids.len() - i,
{
    if i < 0 || i >= ids.len() {
        promises
    } else {
        let id = ids[i];
        let q = PromiseV { callbacks: promises[id].callbacks.insert(awaiter), ..promises[id] };
        spec_callbacks(promises.insert(id, q), ids, awaiter, i + 1)
    }
}

pub open spec fn spec_any_settled(s: StoreV, ids: Seq<Seq<char>>, now: Time, i: int) -> bool
    decreases ids.len() - i,
{
    if i < 0 || i >= ids.len() {
        false
    } else if !s.promises.contains_key(ids[i]) {
        false
    } else {
        spec_project_promise(s.promises[ids[i]], now).state != PromiseState::Pending
            || spec_any_settled(s, ids, now, i + 1)
    }
}

pub open spec fn spec_suspend(req_id: String, version: u64, actions: Seq<PromiseRegisterCallbackReq>, s: StoreV, now: Time) -> Seq<OutV> {
    let ids = spec_awaited(actions);
    let id = req_id@;
    if ids.len() == 0 || ids.contains(id) || !distinct(ids) || !all_in_origin(ids, id) {
        spec_out(spec_status_res(400), s)
    } else {
        match spec_held(s, id, version, now) {
            SpecHeld::Missing => spec_out(spec_status_res(404), s),
            SpecHeld::Stale => spec_out(spec_status_res(409), s),
            SpecHeld::Ok(t) => {
                if exists|i: int| 0 <= i < ids.len() && !s.promises.contains_key(ids[i]) {
                    spec_out(spec_status_res(422), s)
                } else if exists|i: int|
                    0 <= i < ids.len() && !spec_external(s.promises[ids[i]])
                {
                    spec_out(spec_status_res(422), s)
                } else if spec_any_settled(s, ids, now, 0) {
                    let u = TaskV { resumes: Seq::empty(), ..t };
                    spec_out(spec_status_res(300), StoreV { tasks: s.tasks.insert(id, u), ..s })
                } else {
                    let u = TaskV {
                        state: TaskState::Suspended,
                        pid: None,
                        ttl: None,
                        acquired_at: 0,
                        retry_timeout_at: None,
                        resumes: Seq::empty(),
                        ..t
                    };
                    let tasks = s.tasks.insert(id, u);
                    let promises = spec_callbacks(s.promises, ids, id, 0);
                    spec_out(spec_status_res(200), StoreV { promises, tasks, ..s })
                }
            },
        }
    }
}

pub open spec fn spec_wrap_fence(outs: Seq<OutV>, create: bool) -> Seq<OutV> {
    if outs.len() != 1 {
        outs
    } else {
        let o = outs[0];
        match o.resp {
            Response::Promise(inner) => {
                let action = if create { TaskFenceInnerRes::Create(inner) } else { TaskFenceInnerRes::Settle(inner) };
                seq![OutV { resp: spec_fence_res(200, Some(action)), ..o }]
            },
            _ => outs,
        }
    }
}

pub open spec fn spec_fence(req: TaskFenceReq, s: StoreV, now: Time) -> Seq<OutV> {
    let id = req.id;
    let target = match req.action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    if target@ == id@ {
        spec_out(spec_fence_res(400, None), s)
    } else {
        match req.action {
            TaskFenceAction::Settle(st) if !same_origin_spec(st.id@, id@) => {
                spec_out(spec_fence_res(400, None), s)
            },
            TaskFenceAction::Create(c) if !same_origin_spec(c.id@, id@) => {
                spec_out(spec_fence_res(400, None), s)
            },
            action => match spec_held(s, id@, req.version, now) {
                SpecHeld::Missing => spec_out(spec_fence_res(404, None), s),
                SpecHeld::Stale => spec_out(spec_fence_res(409, None), s),
                SpecHeld::Ok(_) => {
                    let create = match action {
                        TaskFenceAction::Create(_) => true,
                        TaskFenceAction::Settle(_) => false,
                    };
                    let inner = match action {
                        TaskFenceAction::Create(c) => spec_promise_create(c, s, now),
                        TaskFenceAction::Settle(st) => spec_promise_settle(st, s, now),
                    };
                    spec_wrap_fence(inner, create)
                },
            },
        }
    }
}

pub open spec fn spec_refs_one_origin(refs: Seq<TaskRef>, j: int) -> bool
    decreases refs.len() - j,
{
    if j < 1 || j >= refs.len() {
        true
    } else {
        origin(refs[j].id@) == origin(refs[0].id@) && spec_refs_one_origin(refs, j + 1)
    }
}

pub open spec fn spec_extend(
    s: StoreV,
    pid: Seq<char>,
    refs: Seq<TaskRef>,
    now: Time,
    i: int,
    tasks: Map<Seq<char>, TaskV>,
) -> Map<Seq<char>, TaskV>
    decreases refs.len() - i,
{
    if i < 0 || i >= refs.len() {
        tasks
    } else {
        let id = refs[i].id@;
        let next = match spec_held(s, id, refs[i].version, now) {
            SpecHeld::Ok(t) if t.pid == Some(pid) => {
                tasks.insert(id, TaskV { acquired_at: now, ..t })
            },
            _ => tasks,
        };
        spec_extend(s, pid, refs, now, i + 1, next)
    }
}

pub open spec fn spec_heartbeat(pid: String, refs: Seq<TaskRef>, s: StoreV, now: Time) -> Seq<OutV> {
    if refs.len() > 0 && !spec_refs_one_origin(refs, 1) {
        spec_out(spec_status_res(400), s)
    } else {
        let tasks = spec_extend(s, pid@, refs, now, 0, s.tasks);
        spec_out(spec_status_res(200), StoreV { tasks, ..s })
    }
}

pub open spec fn spec_schedule_create(req: ScheduleCreateReq, s: StoreV, now: Time) -> Seq<OutV> {
    if spec_is_timer(req.promise_tags) && spec_has_target(req.promise_tags) {
        spec_out(spec_schedule_res(400, None), s)
    } else if s.schedules.contains_key(req.id@) {
        spec_out(spec_schedule_res(200, Some(spec_schedule_value(s.schedules[req.id@]))), s)
    } else {
        let next_run_at = spec_next_cron(req.cron@, now);
        let c = ScheduleV {
            id: req.id@,
            cron: req.cron@,
            promise_id: req.promise_id@,
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param,
            promise_tags: req.promise_tags,
            created_at: now,
            next_run_at,
            last_run_at: None,
        };
        let rec = Schedule {
            id: req.id,
            cron: req.cron,
            promise_id: req.promise_id,
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param,
            promise_tags: req.promise_tags,
            created_at: now,
            next_run_at,
            last_run_at: None,
        };
        spec_out(spec_schedule_res(200, Some(rec)), StoreV { schedules: s.schedules.insert(req.id@, c), ..s })
    }
}

pub open spec fn spec_register_callback(awaited: String, awaiter: String, s: StoreV, now: Time) -> Seq<OutV> {
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        spec_out(spec_promise_res(400, None), s)
    } else if !s.promises.contains_key(awaited@) {
        spec_out(spec_promise_res(404, None), s)
    } else if !s.promises.contains_key(awaiter@) {
        spec_out(spec_promise_res(422, None), s)
    } else {
        let p = spec_project_promise(s.promises[awaited@], now);
        let w = spec_project_promise(s.promises[awaiter@], now);
        let res = spec_promise_res(200, Some(spec_promise_record(awaited, p)));
        if !spec_has_target(w.tags) || !spec_external(p) {
            spec_out(spec_promise_res(422, None), s)
        } else if p.state != PromiseState::Pending || w.state != PromiseState::Pending {
            spec_out(res, s)
        } else {
            let q = PromiseV { callbacks: p.callbacks.insert(awaiter@), ..p };
            spec_out(res, StoreV { promises: s.promises.insert(awaited@, q), ..s })
        }
    }
}

pub open spec fn spec_register_listener(awaited: String, address: String, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.promises.contains_key(awaited@) {
        spec_out(spec_promise_res(404, None), s)
    } else {
        let p = spec_project_promise(s.promises[awaited@], now);
        if !spec_external(p) {
            spec_out(spec_promise_res(422, None), s)
        } else {
            let res = spec_promise_res(200, Some(spec_promise_record(awaited, p)));
            if p.state != PromiseState::Pending {
                spec_out(res, s)
            } else {
                let q = PromiseV { listeners: p.listeners.insert(address@), ..p };
                spec_out(res, StoreV { promises: s.promises.insert(awaited@, q), ..s })
            }
        }
    }
}

pub open spec fn spec_task_acquire(id: String, version: u64, pid: String, ttl: Time, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id@) || !s.promises.contains_key(id@) {
        spec_out(spec_claim_res(404, None, None), s)
    } else {
        let t = s.tasks[id@];
        let p = spec_project_promise(s.promises[id@], now);
        let seen = spec_project_task(t, p);
        if seen.state != TaskState::Pending || p.state != PromiseState::Pending || t.version != version {
            spec_out(spec_claim_res(409, None, None), s)
        } else {
            let u = spec_acquire(t, sat_add(t.version, 1), pid@, ttl, now);
            spec_out(
                spec_claim_res(200, Some(spec_task_record(id, u)), Some(spec_promise_record(id, p))),
                StoreV { tasks: s.tasks.insert(id@, u), ..s },
            )
        }
    }
}

pub open spec fn spec_task_release(id: String, version: u64, s: StoreV, now: Time) -> Seq<OutV> {
    match spec_held(s, id@, version, now) {
        SpecHeld::Missing => spec_out(spec_status_res(404), s),
        SpecHeld::Stale => spec_out(spec_status_res(409), s),
        SpecHeld::Ok(t) => {
            let u = spec_unlease(t, TaskState::Pending, Some(now));
            spec_out(spec_status_res(200), StoreV { tasks: s.tasks.insert(id@, u), ..s })
        },
    }
}

pub open spec fn spec_task_fulfill(id: String, version: u64, action: PromiseSettleReq, s: StoreV, now: Time) -> Seq<OutV> {
    if !action.state.spec_settable() {
        spec_out(spec_promise_res(400, None), s)
    } else {
        match spec_held(s, id@, version, now) {
            SpecHeld::Missing => spec_out(spec_promise_res(404, None), s),
            SpecHeld::Stale => spec_out(spec_promise_res(409, None), s),
            SpecHeld::Ok(_) => {
                let n = spec_settle(s, id@, action.state, action.value, now);
                let res = if n.promises.contains_key(id@) {
                    spec_promise_res(200, Some(spec_promise_record(id, n.promises[id@])))
                } else {
                    spec_promise_res(500, None)
                };
                spec_out(res, n)
            },
        }
    }
}

pub open spec fn spec_task_halt(id: String, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id@) {
        spec_out(spec_status_res(404), s)
    } else {
        let t = s.tasks[id@];
        let seen = if s.promises.contains_key(id@) {
            spec_project_task(t, spec_project_promise(s.promises[id@], now)).state
        } else {
            t.state
        };
        match seen {
            TaskState::Fulfilled => spec_out(spec_status_res(409), s),
            TaskState::Halted => spec_out(spec_status_res(200), s),
            _ => {
                let u = spec_unlease(t, TaskState::Halted, None);
                spec_out(spec_status_res(200), StoreV { tasks: s.tasks.insert(id@, u), ..s })
            },
        }
    }
}

pub open spec fn spec_task_continue(id: String, s: StoreV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id@) {
        spec_out(spec_status_res(404), s)
    } else {
        let t = s.tasks[id@];
        let live = s.promises.contains_key(id@)
            && spec_project_promise(s.promises[id@], now).state == PromiseState::Pending;
        if t.state != TaskState::Halted || !live {
            spec_out(spec_status_res(409), s)
        } else {
            let u = TaskV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t };
            spec_out(spec_status_res(200), StoreV { tasks: s.tasks.insert(id@, u), ..s })
        }
    }
}

pub open spec fn spec_handler(_config: ServerConfig, op: Request, s: StoreV, now: Time) -> Seq<OutV> {
    match op {
        Request::PromiseCreate(c) => spec_promise_create(c, s, now),
        Request::PromiseGet(q) => {
            if !s.promises.contains_key(q.id@) {
                spec_out(spec_promise_res(404, None), s)
            } else {
                let seen = spec_project_promise(s.promises[q.id@], now);
                spec_out(spec_promise_res(200, Some(spec_promise_record(q.id, seen))), s)
            }
        },
        Request::PromiseSettle(st) => spec_promise_settle(st, s, now),
        Request::PromiseRegisterCallback(q) => spec_register_callback(q.awaited, q.awaiter, s, now),
        Request::PromiseRegisterListener(q) => spec_register_listener(q.awaited, q.address, s, now),
        Request::TaskGet(q) => {
            if !s.tasks.contains_key(q.id@) {
                spec_out(spec_task_get_res(404, None), s)
            } else {
                let t = s.tasks[q.id@];
                let seen = if s.promises.contains_key(q.id@) {
                    spec_project_task(t, spec_project_promise(s.promises[q.id@], now))
                } else {
                    t
                };
                spec_out(spec_task_get_res(200, Some(spec_task_record(q.id, seen))), s)
            }
        },
        Request::TaskCreate(q) => spec_task_create(q.pid, q.ttl, q.action, s, now),
        Request::TaskAcquire(q) => spec_task_acquire(q.id, q.version, q.pid, q.ttl, s, now),
        Request::TaskRelease(q) => spec_task_release(q.id, q.version, s, now),
        Request::TaskFulfill(q) => spec_task_fulfill(q.id, q.version, q.action, s, now),
        Request::TaskHeartbeat(q) => spec_heartbeat(q.pid, q.tasks@, s, now),
        Request::TaskSuspend(q) => spec_suspend(q.id, q.version, q.actions@, s, now),
        Request::TaskFence(q) => spec_fence(q, s, now),
        Request::TaskFenceCheck(q) => match spec_held(s, q.id@, q.version, now) {
            SpecHeld::Missing => spec_out(spec_status_res(404), s),
            SpecHeld::Stale => spec_out(spec_status_res(409), s),
            SpecHeld::Ok(_) => spec_out(spec_status_res(200), s),
        },
        Request::TaskHalt(q) => spec_task_halt(q.id, s, now),
        Request::TaskContinue(q) => spec_task_continue(q.id, s, now),
        Request::ScheduleCreate(c) => spec_schedule_create(c, s, now),
        Request::ScheduleGet(q) => {
            if !s.schedules.contains_key(q.id@) {
                spec_out(spec_schedule_res(404, None), s)
            } else {
                spec_out(spec_schedule_res(200, Some(spec_schedule_value(s.schedules[q.id@]))), s)
            }
        },
        Request::ScheduleDelete(q) => {
            if !s.schedules.contains_key(q.id@) {
                spec_out(spec_status_res(404), s)
            } else {
                spec_out(spec_status_res(200), StoreV { schedules: s.schedules.remove(q.id@), ..s })
            }
        },
    }
}


} // verus!
