//! The six named internal actions from `02-abstract/internal.lean`.
//!
//! Internal reads choose their discipline explicitly: touches materialize,
//! lease/retry views do not. They never inherit the external `materialize`
//! switch.

use vstd::prelude::*;
use crate::state::*;
use crate::types::*;

verus! {

pub fn process_promise_timeout_action(
    state: &State, req: &PromiseTimeoutReq, now: u64, _config: &Config,
) -> Vec<Effect> {
    read_object(state, &req.id, now, true).effects
}

fn resume_one(state: &State, awaited: &Ident, awaiter: &Ident, now: u64) -> Vec<Effect> {
    let read = read_task_object(state, awaiter, now, true);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return read.effects,
        Some(t) => t,
    };
    let mut t = t0.dup();
    let mut write = false;
    match t.state {
        TaskState::Suspended => {
            t.state = TaskState::Pending;
            t.resumes = Vec::new();
            t.resumes.push(awaited.dup());
            t.retry_timeout_at = Some(now);
            write = true;
        }
        TaskState::Pending | TaskState::Acquired | TaskState::Halted => {
            let mut found = false;
            let mut i: usize = 0;
            while i < t.resumes.len()
                decreases t.resumes@.len() - i,
            {
                if ident_eq(&t.resumes[i], awaited) { found = true; }
                i += 1;
            }
            if !found {
                t.resumes.push(awaited.dup());
                write = true;
            }
        }
        TaskState::Fulfilled => {}
    }
    let mut effects = read.effects;
    if write { effects.push(Effect::SetTask(o.id, t)); }
    effects
}

pub fn process_callback_action(
    state: &State, req: &PromiseRegisterCallbackReq, now: u64, _config: &Config,
) -> Vec<Effect> {
    let read = read_object(state, &req.awaited, now, true);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    if o.promise.state == PromiseState::Pending {
        return read.effects;
    }
    let mut found = false;
    let mut i: usize = 0;
    while i < o.promise.callbacks.len()
        decreases o.promise.callbacks@.len() - i,
    {
        if ident_eq(&o.promise.callbacks[i], &req.awaiter) { found = true; }
        i += 1;
    }
    if !found { return read.effects; }
    let mut effects = read.effects;
    effects.push(Effect::SetPromise(
        o.id.dup(), o.promise.dup().remove_callback(&req.awaiter),
    ));
    append_effects(effects, resume_one(state, &o.id, &req.awaiter, now))
}

pub fn process_listener_action(
    state: &State, req: &PromiseRegisterListenerReq, now: u64, _config: &Config,
) -> Vec<Effect> {
    let read = read_object(state, &req.awaited, now, true);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    if o.promise.state == PromiseState::Pending {
        return read.effects;
    }
    let mut found = false;
    let mut i: usize = 0;
    while i < o.promise.listeners.len()
        decreases o.promise.listeners@.len() - i,
    {
        if text_eq(&o.promise.listeners[i], &req.address) { found = true; }
        i += 1;
    }
    if !found { return read.effects; }
    let mut effects = read.effects;
    effects.push(Effect::SetPromise(
        o.id.dup(), o.promise.dup().remove_listener(&req.address),
    ));
    effects.push(Effect::SetMessage(
        req.address.dup(),
        Message {
            kind: MessageKind::Unblock, task_id: None, version: 0,
            promise: Some(o.promise.to_record(&o.id)),
        },
    ));
    effects
}

pub fn process_lease_timeout_action(
    state: &State, req: &TaskLeaseTimeoutReq, now: u64, _config: &Config,
) -> Vec<Effect> {
    let read = read_task_object(state, &req.id, now, false);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return read.effects,
        Some(t) => t,
    };
    let deadline = match t0.lease_timeout_at {
        None => return read.effects,
        Some(x) => x,
    };
    let mut effects = read.effects;
    if t0.state == TaskState::Acquired && deadline <= now
        && o.promise.state == PromiseState::Pending
    {
        let mut t = t0.dup();
        t.state = TaskState::Pending;
        t.pid = None;
        t.ttl = None;
        t.lease_timeout_at = None;
        t.retry_timeout_at = Some(now);
        effects.push(Effect::SetTask(o.id, t));
    }
    effects
}

pub fn process_retry_timeout_action(
    state: &State, req: &TaskRetryTimeoutReq, now: u64, config: &Config,
) -> Vec<Effect> {
    let read = read_task_object(state, &req.id, now, false);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    let t0 = match &o.task {
        None => return read.effects,
        Some(t) => t,
    };
    let due = match t0.retry_timeout_at {
        None => return read.effects,
        Some(x) => x,
    };
    let mut effects = read.effects;
    if t0.state == TaskState::Pending && due <= now
        && o.promise.state == PromiseState::Pending
    {
        let mut t = t0.dup();
        t.retry_timeout_at = Some(checked_add(now, config.retry_timeout));
        effects.push(Effect::SetTask(o.id.dup(), t));
        let address = match tag_value(&o.promise.tags, 0) {
            Some(x) => x,
            None => Text::empty(),
        };
        effects.push(Effect::SetMessage(
            address,
            Message {
                kind: MessageKind::Execute, task_id: Some(o.id), version: t0.version,
                promise: None,
            },
        ));
    }
    effects
}

fn fire_occurrence(
    state: &State, schedule: &Schedule, occurrence: &Occurrence,
) -> Vec<Effect> {
    // `createIfAbsent` sees the transition's pre-state, not earlier effects.
    let read = read_object(state, &occurrence.promise_id, occurrence.at, true);
    match read.object {
        Some(_) => read.effects,
        None => {
            let req = PromiseCreateReq {
                id: occurrence.promise_id.dup(),
                timeout_at: checked_add(occurrence.at, schedule.promise_timeout),
                param: schedule.promise_param.dup(),
                tags: dup_tags(&schedule.promise_tags),
            };
            let made = create_promise(req, occurrence.at);
            append_effects(read.effects, made.effects)
        }
    }
}

pub fn process_schedule_action(
    state: &State, req: &ScheduleTimeoutReq, now: u64, _config: &Config,
) -> Vec<Effect> {
    let si = match state.find_schedule(&req.schedule) {
        None => return Vec::new(),
        Some(i) => i,
    };
    let schedule = &state.schedules[si];
    let mut effects = Vec::new();
    let mut last: Option<u64> = None;
    let mut i: usize = 0;
    // The request carries Lean's opaque `occurrences` result in list order.
    // The filter is stable, exactly `List.filter (· ≤ now)`.
    while i < req.occurrences.len()
        decreases req.occurrences@.len() - i,
    {
        if req.occurrences[i].at <= now {
            effects = append_effects(
                effects, fire_occurrence(state, schedule, &req.occurrences[i]),
            );
            last = Some(req.occurrences[i].at);
        }
        i += 1;
    }
    match last {
        None => effects,
        Some(at) => {
            let mut next = schedule.dup();
            next.last_run_at = Some(at);
            next.next_run_at = req.next_run_at;
            effects.push(Effect::SetSchedule(next));
            effects
        }
    }
}

} // verus!
