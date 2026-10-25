//! The Resonate model's requests and responses in the kernel's vocabulary,
//! and back: what `dispatch.rs` and the drivers' `wire.rs` do on the wire,
//! as spec functions over the views.

use vstd::prelude::*;

use echod_kernel::tags::{tags_get, tags_has};
use echod_kernel::types::*;
use resonate::collections::{spec_address_valid, spec_settable};
use resonate::twins::*;
use resonate::{PState, TState, Tags};

verus! {

/// The one worker every targeted promise names (the simulator's).
pub open spec fn worker() -> Chars {
    "sim://worker"@
}

pub open spec fn key_target() -> Chars { "resonate:target"@ }
pub open spec fn key_external() -> Chars { "resonate:external"@ }
pub open spec fn key_timer() -> Chars { "resonate:timer"@ }
pub open spec fn key_delay() -> Chars { "resonate:delay"@ }
pub open spec fn tru() -> Chars { "true"@ }

/// `wire::create_tags`: the model's four tags as the kernel's sorted pairs. A
/// timer's target is dropped on the way in (an SDK's sleep), as `create_tags`
/// drops it.
pub open spec fn tags_in(t: Tags) -> ATags {
    let delay: ATags = match t.delay {
        Some(d) => seq![(key_delay(), nat_chars(d as nat))],
        None => Seq::empty(),
    };
    let external: ATags = if t.external { seq![(key_external(), tru())] } else { Seq::empty() };
    let target: ATags = if t.target && !t.timer { seq![(key_target(), worker())] } else { Seq::empty() };
    let timer: ATags = if t.timer { seq![(key_timer(), tru())] } else { Seq::empty() };
    delay + external + target + timer
}

/// The decimal digits of `n`, as the wire carries a delay.
pub uninterp spec fn nat_chars(n: nat) -> Chars;

#[verifier::external_body]
pub proof fn axiom_nat_chars(n: nat)
    ensures
        spec_parse_nat(nat_chars(n)) == n,
{
}

/// `wire::tags_in`: the kernel's pairs as the model's four tags.
pub open spec fn tags_out(t: ATags) -> Tags {
    Tags {
        target: tags_has(t, key_target()),
        external: tags_get(t, key_external()) == Some(tru()),
        timer: tags_get(t, key_timer()) == Some(tru()),
        delay: match tags_get(t, key_delay()) {
            Some(d) => Some(spec_parse_nat(d) as u64),
            None => None,
        },
    }
}

pub open spec fn value_in(data: Option<Chars>) -> AValue {
    AValue { headers: Seq::empty(), data }
}

pub open spec fn value_out(v: AValue) -> Option<Chars> {
    v.data
}

pub open spec fn pstate_in(s: PState) -> PromiseState {
    match s {
        PState::Pending => PromiseState::Pending,
        PState::Resolved => PromiseState::Resolved,
        PState::Rejected => PromiseState::Rejected,
        PState::Canceled => PromiseState::RejectedCanceled,
        PState::TimedOut => PromiseState::RejectedTimedout,
    }
}

pub open spec fn pstate_out(s: PromiseState) -> PState {
    match s {
        PromiseState::Pending => PState::Pending,
        PromiseState::Resolved => PState::Resolved,
        PromiseState::Rejected => PState::Rejected,
        PromiseState::RejectedCanceled => PState::Canceled,
        PromiseState::RejectedTimedout => PState::TimedOut,
    }
}

pub open spec fn tstate_out(s: TaskState) -> TState {
    match s {
        TaskState::Pending => TState::Pending,
        TaskState::Acquired => TState::Acquired,
        TaskState::Suspended => TState::Suspended,
        TaskState::Halted => TState::Halted,
        TaskState::Fulfilled => TState::Fulfilled,
    }
}

pub open spec fn create_in(c: CreateV) -> APromiseCreateReq {
    APromiseCreateReq { id: c.id, timeout_at: c.timeout_at, param: value_in(c.data), tags: tags_in(c.tags) }
}

/// `wire::settle_in`: the model's state name as the kernel's state; a name
/// that is not a settled state does not parse (400).
pub open spec fn settle_in(st: SettleV) -> Option<APromiseSettleReq> {
    match spec_settable(st.state) {
        Some(s) => Some(APromiseSettleReq { id: st.id, state: pstate_in(s), value: value_in(st.data) }),
        None => None,
    }
}

/// What a request becomes in front of the kernel.
pub enum Plan {
    /// Refused by the wire rules.
    Refuse(u16),
    /// One kernel request.
    One(ARequest),
    /// A fence creating in another origin: the create first, as a request of
    /// its own, then the fence's check.
    Detached(APromiseCreateReq, ATaskFenceCheckReq),
}

/// `dispatch::decode` on the model's request: the wire rules, then the kernel
/// request. A `u32` version becomes the kernel's `u64`.
pub open spec fn plan(req: RequestV) -> Plan {
    match req {
        RequestV::CreatePromise(c) => {
            if c.tags.target && !c.tags.timer && !spec_address_valid(worker()) {
                Plan::Refuse(400)
            } else {
                Plan::One(ARequest::PromiseCreate(create_in(c)))
            }
        },
        RequestV::GetPromise(id) => Plan::One(ARequest::PromiseGet(APromiseGetReq { id })),
        RequestV::SettlePromise(st) => match settle_in(st) {
            Some(q) => Plan::One(ARequest::PromiseSettle(q)),
            None => Plan::Refuse(400),
        },
        RequestV::RegisterCallback { awaited, awaiter } => Plan::One(ARequest::PromiseRegisterCallback(APromiseRegisterCallbackReq { awaited, awaiter })),
        RequestV::RegisterListener { awaited, address } => {
            if !spec_address_valid(address) {
                Plan::Refuse(400)
            } else {
                Plan::One(ARequest::PromiseRegisterListener(APromiseRegisterListenerReq { awaited, address }))
            }
        },
        RequestV::GetTask(id) => Plan::One(ARequest::TaskGet(ATaskGetReq { id })),
        RequestV::CreateTask { pid, ttl, action } => Plan::One(ARequest::TaskCreate(ATaskCreateReq { pid, ttl, action: create_in(action) })),
        RequestV::AcquireTask { id, version, pid, ttl } => Plan::One(ARequest::TaskAcquire(ATaskAcquireReq { id, version: version as u64, pid, ttl })),
        RequestV::ReleaseTask { id, version } => Plan::One(ARequest::TaskRelease(ATaskReleaseReq { id, version: version as u64 })),
        RequestV::FulfillTask { id, version, state, data } => match settle_in(SettleV { id, state, data }) {
            Some(q) => Plan::One(ARequest::TaskFulfill(ATaskFulfillReq { id, version: version as u64, action: q })),
            None => Plan::Refuse(400),
        },
        RequestV::HeartbeatTask { pid, tasks } => Plan::One(ARequest::TaskHeartbeat(ATaskHeartbeatReq {
            pid,
            tasks: tasks.map_values(|r: TaskRefV| ATaskRef { id: r.id, version: r.version as u64 }),
        })),
        RequestV::SuspendTask { id, version, awaited } => Plan::One(ARequest::TaskSuspend(ATaskSuspendReq {
            id,
            version: version as u64,
            actions: awaited.map_values(|a: Chars| APromiseRegisterCallbackReq { awaited: a, awaiter: id }),
        })),
        RequestV::FenceTask { id, version, action } => match action {
            FencedV::Create(c) => {
                if c.tags.target && !c.tags.timer && !spec_address_valid(worker()) {
                    Plan::Refuse(400)
                } else if origin(c.id) != origin(id) {
                    Plan::Detached(create_in(c), ATaskFenceCheckReq { id, version: version as u64 })
                } else {
                    Plan::One(ARequest::TaskFence(ATaskFenceReq { id, version: version as u64, action: ATaskFenceAction::Create(create_in(c)) }))
                }
            },
            FencedV::Settle(st) => match settle_in(st) {
                None => Plan::Refuse(400),
                Some(q) => {
                    if origin(st.id) != origin(id) {
                        Plan::Refuse(400)
                    } else {
                        Plan::One(ARequest::TaskFence(ATaskFenceReq { id, version: version as u64, action: ATaskFenceAction::Settle(q) }))
                    }
                },
            },
        },
        RequestV::HaltTask(id) => Plan::One(ARequest::TaskHalt(ATaskHaltReq { id })),
        RequestV::ContinueTask(id) => Plan::One(ARequest::TaskContinue(ATaskContinueReq { id })),
        // schedules: out of the store machine's scope for now
        RequestV::CreateSchedule(_) => Plan::Refuse(501),
        RequestV::GetSchedule(_) => Plan::Refuse(501),
        RequestV::DeleteSchedule(_) => Plan::Refuse(501),
    }
}

/// The origin of an id: the model's `origin`, which the kernel's
/// `origin_of` agrees with (both the part before the first `:`).
pub open spec fn origin(id: Chars) -> Chars {
    resonate::collections::origin(id)
}

// ----------------------------------------------------------------- responses

pub open spec fn prec_out(r: APromiseRecord) -> PromiseRecV {
    PromiseRecV {
        id: r.id,
        state: pstate_out(r.state),
        param: value_out(r.param),
        value: value_out(r.value),
        timeout_at: r.timeout_at,
        created_at: r.created_at,
        settled_at: r.settled_at,
        tags: tags_out(r.tags),
    }
}

pub open spec fn trec_out(r: ATaskRecord) -> TaskRecV {
    TaskRecV {
        id: r.id,
        state: tstate_out(r.state),
        version: r.version as u32,
        pid: r.pid,
        ttl: r.ttl,
        resumes: r.resumes as u32,
    }
}

pub open spec fn promise_res_out(r: APromiseRes) -> ResponseV {
    if r.status != 200 {
        ResponseV::Status(r.status)
    } else {
        match r.promise {
            Some(p) => ResponseV::Promise(prec_out(p)),
            None => ResponseV::Status(200),
        }
    }
}

/// `wire::decode`: the kernel's answer as the model types it.
pub open spec fn response_out(r: AResponse) -> ResponseV {
    match r {
        AResponse::Promise(p) => promise_res_out(p),
        AResponse::Status(s) => ResponseV::Status(s.status),
        AResponse::TaskGet(t) => {
            if t.status != 200 {
                ResponseV::Status(t.status)
            } else {
                match t.task {
                    Some(rec) => ResponseV::Task(trec_out(rec)),
                    None => ResponseV::Status(200),
                }
            }
        },
        AResponse::TaskClaim(c) => {
            if c.status != 200 {
                ResponseV::Status(c.status)
            } else {
                match (c.promise, c.task) {
                    (Some(p), Some(t)) => ResponseV::Both(prec_out(p), trec_out(t)),
                    (None, Some(t)) => ResponseV::Task(trec_out(t)),
                    (Some(p), None) => ResponseV::Promise(prec_out(p)),
                    (None, None) => ResponseV::Status(200),
                }
            }
        },
        AResponse::TaskFence(f) => {
            if f.status != 200 {
                ResponseV::Status(f.status)
            } else {
                match f.action {
                    Some(ATaskFenceInnerRes::Create(p)) => promise_res_out(p),
                    Some(ATaskFenceInnerRes::Settle(p)) => promise_res_out(p),
                    None => ResponseV::Status(200),
                }
            }
        },
        AResponse::Schedule(s) => ResponseV::Status(s.status),
    }
}

/// An outbox entry as the dispatch a client receives.
pub open spec fn message_out(e: AOutboxEntry) -> DispatchV {
    match e.message {
        AMessage::Execute { task_id, version } => DispatchV::Execute { id: task_id, version: version as u32 },
        AMessage::Unblock(r) => DispatchV::Unblock { address: e.address, promise: prec_out(r) },
    }
}

} // verus!
