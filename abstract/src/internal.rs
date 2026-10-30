//! The six named internal actions from `02-abstract/internal.lean`.
//!
//! Internal reads choose their discipline explicitly: touches materialize,
//! lease/retry views do not. They never inherit the external `materialize`
//! switch.

use vstd::prelude::*;
use crate::state::*;
use crate::types::*;

verus! {

// -------------------------------------------------------------------------
// Independent ghost semantics
// -------------------------------------------------------------------------
//
// These definitions are the proof model for the Lean reader/writer
// handlers.  They mention only this crate's Abstract vocabulary.  In
// particular, every nested read is from the original `state`; effects are
// concatenated in writer order and are never fed back into a later read.

pub open spec fn internal_sat_add(a: u64, b: u64) -> u64 {
    if b <= u64::MAX - a { (a + b) as u64 } else { u64::MAX }
}

pub open spec fn internal_project_promise(p: APromiseObject, now: u64) -> APromiseObject {
    spec_project_promise(p, now)
}

pub open spec fn internal_fulfill_task(t: ATaskObject) -> ATaskObject {
    spec_fulfill_task(t)
}

pub open spec fn internal_project_object(o: AObject, now: u64) -> AObject {
    spec_project_object(o, now)
}

pub open spec fn internal_read_object(
    state: AState, id: AIdent, now: u64,
) -> Option<AObject> {
    spec_read_object(state, id, now)
}

pub open spec fn internal_read_effects(
    state: AState, id: AIdent, now: u64, materialize: bool,
) -> Seq<AEffect> {
    spec_read_effects(state, id, now, materialize)
}

pub open spec fn internal_read_task_object(
    state: AState, id: AIdent, now: u64,
) -> Option<AObject> {
    spec_read_task_object(state, id, now)
}

pub open spec fn internal_read_task_effects(
    state: AState, id: AIdent, now: u64, materialize: bool,
) -> Seq<AEffect> {
    spec_read_task_effects(state, id, now, materialize)
}

pub open spec fn internal_without_ident(xs: Seq<AIdent>, id: AIdent) -> Seq<AIdent>
{
    spec_without_ident(xs, id)
}

pub open spec fn internal_without_text(xs: Seq<AText>, x: AText) -> Seq<AText>
{
    spec_without_text(xs, x)
}

pub open spec fn internal_promise_record(p: APromiseObject, id: AIdent) -> APromiseRecord {
    APromiseRecord {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        tags: p.tags,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

pub open spec fn promise_timeout_semantics(
    state: AState, req: APromiseTimeoutReq, now: u64,
) -> Seq<AEffect> {
    internal_read_effects(state, req.id, now, true)
}

/// `resumeOne`: a suspended awaiter wakes with its first offer due at
/// `since`, the instant the awaited promise settled, not the instant the
/// callback happened to be processed.
pub open spec fn resume_one_semantics(
    state: AState, awaited: AIdent, awaiter: AIdent, now: u64, since: u64,
) -> Seq<AEffect> {
    let reads = internal_read_task_effects(state, awaiter, now, true);
    match internal_read_task_object(state, awaiter, now) {
        Some(o) => match o.task {
            Some(t) => {
                let write = match t.state {
                    TaskState::Suspended => Some(ATaskObject {
                        state: TaskState::Pending,
                        resumes: seq![awaited],
                        retry_timeout_at: Some(since),
                        ..t
                    }),
                    TaskState::Pending | TaskState::Acquired | TaskState::Halted =>
                        if t.resumes.contains(awaited) {
                            None
                        } else {
                            Some(ATaskObject { resumes: t.resumes.push(awaited), ..t })
                        },
                    TaskState::Fulfilled => None,
                };
                match write {
                    Some(next) => reads + seq![AEffect::SetTask(o.id, next)],
                    None => reads,
                }
            }
            None => reads,
        },
        None => reads,
    }
}

pub open spec fn settled_since(p: APromiseObject) -> u64 {
    match p.settled_at {
        Some(x) => x,
        None => 0,
    }
}

pub open spec fn callback_semantics(
    state: AState, req: APromiseRegisterCallbackReq, now: u64,
) -> Seq<AEffect> {
    let reads = internal_read_effects(state, req.awaited, now, true);
    match internal_read_object(state, req.awaited, now) {
        Some(o) if o.promise.state != PromiseState::Pending
            && o.promise.callbacks.contains(req.awaiter) => {
            let promise = APromiseObject {
                callbacks: internal_without_ident(o.promise.callbacks, req.awaiter),
                ..o.promise
            };
            reads
                + seq![AEffect::SetPromise(o.id, promise)]
                + resume_one_semantics(
                    state, o.id, req.awaiter, now, settled_since(o.promise),
                )
        }
        _ => reads,
    }
}

pub open spec fn listener_semantics(
    state: AState, req: APromiseRegisterListenerReq, now: u64,
) -> Seq<AEffect> {
    let reads = internal_read_effects(state, req.awaited, now, true);
    match internal_read_object(state, req.awaited, now) {
        Some(o) if o.promise.state != PromiseState::Pending
            && o.promise.listeners.contains(req.address) => {
            let promise = APromiseObject {
                listeners: internal_without_text(o.promise.listeners, req.address),
                ..o.promise
            };
            let message = AMessage {
                kind: MessageKind::Unblock,
                task_id: None,
                version: 0,
                promise: Some(internal_promise_record(o.promise, o.id)),
            };
            reads
                + seq![AEffect::SetPromise(o.id, promise)]
                + seq![AEffect::SetMessage(req.address, message)]
        }
        _ => reads,
    }
}

/// `processLeaseTimeout`: a lapsed lease returns the task to pending with
/// its first offer due at the lease's end, which is when the lapse happened,
/// whenever the node gets to it.
pub open spec fn lease_timeout_semantics(
    state: AState, req: ATaskLeaseTimeoutReq, now: u64,
) -> Seq<AEffect> {
    let reads = internal_read_task_effects(state, req.id, now, false);
    match internal_read_task_object(state, req.id, now) {
        Some(o) => match o.task {
            Some(t) => match t.lease_timeout_at {
                Some(deadline) if t.state == TaskState::Acquired && deadline <= now
                    && o.promise.state == PromiseState::Pending => {
                    let next = ATaskObject {
                        state: TaskState::Pending,
                        pid: None,
                        ttl: None,
                        lease_timeout_at: None,
                        retry_timeout_at: Some(deadline),
                        ..t
                    };
                    reads + seq![AEffect::SetTask(o.id, next)]
                }
                _ => reads,
            },
            None => reads,
        },
        None => reads,
    }
}

pub open spec fn internal_tag_key_target(k: Seq<char>) -> bool {
    spec_tag_key(k, 0)
}

pub open spec fn internal_target_value(tags: ATags) -> Option<AText> {
    spec_tag_value(tags, 0)
}

pub open spec fn internal_target_or_empty(tags: ATags) -> AText {
    match internal_target_value(tags) {
        Some(x) => x,
        None => AText { chars: Seq::empty() },
    }
}

/// `processRetryTimeout`: a due offer is made and the next one armed on the
/// task's own grid, `due + k * retry_timeout`, not `now + retry_timeout`.
pub open spec fn retry_timeout_semantics(
    state: AState, req: ATaskRetryTimeoutReq, now: u64, retry_timeout: u64,
) -> Seq<AEffect> {
    let reads = internal_read_task_effects(state, req.id, now, false);
    match internal_read_task_object(state, req.id, now) {
        Some(o) => match o.task {
            Some(t) => match t.retry_timeout_at {
                Some(due) if t.state == TaskState::Pending && due <= now
                    && o.promise.state == PromiseState::Pending => {
                    let next = ATaskObject {
                        retry_timeout_at: Some(spec_next_offer(due, now, retry_timeout)),
                        ..t
                    };
                    let message = AMessage {
                        kind: MessageKind::Execute,
                        task_id: Some(o.id),
                        version: t.version,
                        promise: None,
                    };
                    reads
                        + seq![AEffect::SetTask(o.id, next)]
                        + seq![AEffect::SetMessage(
                            internal_target_or_empty(o.promise.tags), message,
                        )]
                }
                _ => reads,
            },
            None => reads,
        },
        None => reads,
    }
}

// Schedules ---------------------------------------------------------------
//
// A schedule's firing is two actions, not one, because the occurrence's
// promise and the schedule are different objects and this model claims no
// atomicity across objects. `ScheduleFire` creates the occurrence's promise
// if it is absent; `ScheduleAdvance` moves the schedule past the occurrence
// and is enabled only once that promise exists. Between the two, a client may
// see the promise beside the unadvanced schedule; after a crash between the
// two, the fire runs again, finds the promise, and the advance follows. An
// occurrence is therefore never lost, and never created twice.

/// The create request an occurrence stands for: the template's tags
/// stripped of any earlier stamp, then stamped with the schedule and the
/// promise's own lineage.
pub open spec fn occurrence_create_req(
    schedule: ASchedule, occurrence: AOccurrence,
) -> APromiseCreateReq {
    APromiseCreateReq {
        id: occurrence.promise_id,
        timeout_at: internal_sat_add(occurrence.at, schedule.promise_timeout),
        param: schedule.promise_param,
        tags: spec_stamp(schedule.promise_tags, schedule.id, occurrence.promise_id),
    }
}

/// `createIfAbsent`, as of the occurrence's own instant.
pub open spec fn fire_occurrence_semantics(
    state: AState, schedule: ASchedule, occurrence: AOccurrence,
) -> Seq<AEffect> {
    let reads = internal_read_effects(
        state, occurrence.promise_id, occurrence.at, true,
    );
    match internal_read_object(state, occurrence.promise_id, occurrence.at) {
        Some(_) => reads,
        None => reads + spec_create_promise_effects(
            occurrence_create_req(schedule, occurrence), occurrence.at,
        ),
    }
}

/// The occurrence is one the schedule owes: at or after its next run, and
/// not in the future.
pub open spec fn occurrence_due(
    schedule: ASchedule, occurrence: AOccurrence, now: u64,
) -> bool {
    schedule.next_run_at <= occurrence.at && occurrence.at <= now
}

pub open spec fn schedule_fire_semantics(
    state: AState, req: AScheduleFireReq, now: u64,
) -> Seq<AEffect> {
    match spec_find_schedule(state.schedules, req.schedule) {
        None => Seq::empty(),
        Some(schedule) => if occurrence_due(schedule, req.occurrence, now) {
            fire_occurrence_semantics(state, schedule, req.occurrence)
        } else {
            Seq::empty()
        },
    }
}

/// The advance is enabled only once the occurrence's promise exists.
pub open spec fn advance_enabled(
    state: AState, schedule: ASchedule, req: AScheduleAdvanceReq, now: u64,
) -> bool {
    &&& occurrence_due(schedule, req.occurrence, now)
    &&& req.occurrence.at < req.next_run_at
    &&& spec_find_object(state.objects, req.occurrence.promise_id) is Some
}

pub open spec fn advanced_schedule(
    schedule: ASchedule, req: AScheduleAdvanceReq,
) -> ASchedule {
    ASchedule {
        last_run_at: Some(req.occurrence.at),
        next_run_at: req.next_run_at,
        ..schedule
    }
}

pub open spec fn schedule_advance_semantics(
    state: AState, req: AScheduleAdvanceReq, now: u64,
) -> Seq<AEffect> {
    match spec_find_schedule(state.schedules, req.schedule) {
        None => Seq::empty(),
        Some(schedule) => if advance_enabled(state, schedule, req, now) {
            seq![AEffect::SetSchedule(advanced_schedule(schedule, req))]
        } else {
            Seq::empty()
        },
    }
}

fn ident_vec_contains(xs: &Vec<Ident>, id: &Ident) -> (r: bool)
    ensures r == xs.deep_view().contains(id@),
{
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            forall|j: int| 0 <= j < i ==> xs.deep_view()[j] != id@,
        decreases xs@.len() - i,
    {
        if ident_eq(&xs[i], id) {
            assert(exists|j: int| 0 <= j < xs.deep_view().len()
                && xs.deep_view()[j] == id@) by {
                assert(xs.deep_view()[i as int] == id@);
            }
            assert(xs.deep_view().contains(id@));
            return true;
        }
        i += 1;
    }
    assert(!xs.deep_view().contains(id@)) by {
        if xs.deep_view().contains(id@) {
            let j = choose|j: int| 0 <= j < xs.deep_view().len()
                && xs.deep_view()[j] == id@;
            assert(false);
        }
    }
    false
}

fn text_vec_contains(xs: &Vec<Text>, x: &Text) -> (r: bool)
    ensures r == xs.deep_view().contains(x@),
{
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            i <= xs@.len(),
            forall|j: int| 0 <= j < i ==> xs.deep_view()[j] != x@,
        decreases xs@.len() - i,
    {
        if text_eq(&xs[i], x) {
            assert(exists|j: int| 0 <= j < xs.deep_view().len()
                && xs.deep_view()[j] == x@) by {
                assert(xs.deep_view()[i as int] == x@);
            }
            assert(xs.deep_view().contains(x@));
            return true;
        }
        i += 1;
    }
    assert(!xs.deep_view().contains(x@)) by {
        if xs.deep_view().contains(x@) {
            let j = choose|j: int| 0 <= j < xs.deep_view().len()
                && xs.deep_view()[j] == x@;
            assert(false);
        }
    }
    false
}

pub fn process_promise_timeout_action(
    state: &State, req: &PromiseTimeoutReq, now: u64, _config: &Config,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view() == promise_timeout_semantics(state@, req@, now),
{
    read_object(state, &req.id, now, true).effects
}

fn resume_one(
    state: &State, awaited: &Ident, awaiter: &Ident, now: u64, since: u64,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view()
        == resume_one_semantics(state@, awaited@, awaiter@, now, since),
{
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
    let ghost original = t0.deep_view();
    let mut write = false;
    match t.state {
        TaskState::Suspended => {
            t.state = TaskState::Pending;
            t.resumes = Vec::new();
            t.resumes.push(awaited.dup());
            t.retry_timeout_at = Some(since);
            assert(t.deep_view().state == TaskState::Pending);
            assert(t.deep_view().version == original.version);
            assert(t.deep_view().ttl == original.ttl);
            assert(t.deep_view().pid == original.pid);
            assert(t.deep_view().lease_timeout_at == original.lease_timeout_at);
            assert(t.deep_view().retry_timeout_at == Some(since));
            assert(t.deep_view().resumes =~= seq![awaited@]);
            assert(t.deep_view() == (ATaskObject {
                state: TaskState::Pending,
                resumes: seq![awaited@],
                retry_timeout_at: Some(since),
                ..original
            }));
            write = true;
        }
        TaskState::Pending | TaskState::Acquired | TaskState::Halted => {
            let found = ident_vec_contains(&t.resumes, awaited);
            if !found {
                let ghost before = t.resumes.deep_view();
                t.resumes.push(awaited.dup());
                assert(t.resumes.deep_view() =~= before.push(awaited@));
                assert(t.deep_view() == (ATaskObject {
                    resumes: original.resumes.push(awaited@),
                    ..original
                }));
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
) -> (effects: Vec<Effect>)
    ensures effects.deep_view() == callback_semantics(state@, req@, now),
{
    let read = read_object(state, &req.awaited, now, true);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    if o.promise.state == PromiseState::Pending {
        return read.effects;
    }
    let found = ident_vec_contains(&o.promise.callbacks, &req.awaiter);
    if !found { return read.effects; }
    let since = match o.promise.settled_at { Some(x) => x, None => 0 };
    assert(since == settled_since(o.promise@));
    let mut effects = read.effects;
    effects.push(Effect::SetPromise(
        o.id.dup(), o.promise.dup().remove_callback(&req.awaiter),
    ));
    append_effects(effects, resume_one(state, &o.id, &req.awaiter, now, since))
}

pub fn process_listener_action(
    state: &State, req: &PromiseRegisterListenerReq, now: u64, _config: &Config,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view() == listener_semantics(state@, req@, now),
{
    let read = read_object(state, &req.awaited, now, true);
    let o = match read.object {
        None => return read.effects,
        Some(o) => o,
    };
    if o.promise.state == PromiseState::Pending {
        return read.effects;
    }
    let found = text_vec_contains(&o.promise.listeners, &req.address);
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
) -> (effects: Vec<Effect>)
    ensures effects.deep_view() == lease_timeout_semantics(state@, req@, now),
{
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
        t.retry_timeout_at = Some(deadline);
        effects.push(Effect::SetTask(o.id, t));
    }
    effects
}

pub fn process_retry_timeout_action(
    state: &State, req: &TaskRetryTimeoutReq, now: u64, config: &Config,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view()
        == retry_timeout_semantics(state@, req@, now, config.retry_timeout),
{
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
        t.retry_timeout_at = Some(next_offer(due, now, config.retry_timeout));
        assert(t.deep_view() == (ATaskObject {
            retry_timeout_at: Some(spec_next_offer(due, now, config.retry_timeout)),
            ..t0.deep_view()
        }));
        effects.push(Effect::SetTask(o.id.dup(), t));
        let address = match tag_value(&o.promise.tags, 0) {
            Some(x) => x,
            None => Text::empty(),
        };
        assert(address@ == internal_target_or_empty(o.promise@.tags));
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
) -> (effects: Vec<Effect>)
    ensures effects.deep_view()
        == fire_occurrence_semantics(state@, schedule@, occurrence@),
{
    // `createIfAbsent` sees the transition's pre-state, not earlier effects.
    let read = read_object(state, &occurrence.promise_id, occurrence.at, true);
    match read.object {
        Some(_) => read.effects,
        None => {
            let req = PromiseCreateReq {
                id: occurrence.promise_id.dup(),
                timeout_at: checked_add(occurrence.at, schedule.promise_timeout),
                param: schedule.promise_param.dup(),
                tags: stamp_tags(&schedule.promise_tags, &schedule.id, &occurrence.promise_id),
            };
            assert(req@ == occurrence_create_req(schedule@, occurrence@));
            let made = create_promise(req, occurrence.at);
            append_effects(read.effects, made.effects)
        }
    }
}

pub fn process_schedule_fire_action(
    state: &State, req: &ScheduleFireReq, now: u64, _config: &Config,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view() == schedule_fire_semantics(state@, req@, now),
{
    let si = match state.find_schedule(&req.schedule) {
        None => return Vec::new(),
        Some(i) => i,
    };
    let schedule = &state.schedules[si];
    if !(schedule.next_run_at <= req.occurrence.at && req.occurrence.at <= now) {
        return Vec::new();
    }
    fire_occurrence(state, schedule, &req.occurrence)
}

pub fn process_schedule_advance_action(
    state: &State, req: &ScheduleAdvanceReq, now: u64, _config: &Config,
) -> (effects: Vec<Effect>)
    ensures effects.deep_view() == schedule_advance_semantics(state@, req@, now),
{
    let si = match state.find_schedule(&req.schedule) {
        None => return Vec::new(),
        Some(i) => i,
    };
    let schedule = &state.schedules[si];
    if !(schedule.next_run_at <= req.occurrence.at && req.occurrence.at <= now
        && req.occurrence.at < req.next_run_at)
    {
        return Vec::new();
    }
    // The promise first: an advance never outruns the occurrence it stands for.
    if state.find_object(&req.occurrence.promise_id).is_none() {
        return Vec::new();
    }
    let mut next = schedule.dup();
    next.last_run_at = Some(req.occurrence.at);
    next.next_run_at = req.next_run_at;
    assert(next@ == advanced_schedule(schedule@, req@));
    let mut effects = Vec::new();
    effects.push(Effect::SetSchedule(next));
    assert(effects.deep_view() =~= seq![AEffect::SetSchedule(advanced_schedule(schedule@, req@))]);
    effects
}

} // verus!
