//! Trace inclusion: every run of the Concrete document is a run of the
//! Abstract.
//!
//! The Concrete document moves by the kernel's steps, each a spec function
//! of the document (`echod_kernel`): a sweep (`executable_single_pass`), a
//! request handled (`spec_handle`), a schedule fired (`spec_fire`). The
//! node composes them (`logic::flight::decide`): a request is sweep,
//! handle, sweep; a timer is a sweep; a schedule is fire, sweep. Any such
//! composition is a sequence of micro steps, so the theorem is stated on
//! those: for every sequence of micro steps that the kernel admits, there is
//! a sequence of Abstract actions, external and internal, running to a
//! related state and answering the same responses in the same order.
//!
//! The witness is constructive: `micro_actions` names the Abstract actions
//! each kernel step is, so the theorem is `trace_actions`, not an
//! existential alone.

use vstd::prelude::*;

use echod_abstract::promise_spec as pspec;
use echod_abstract::schedule_spec as sspec;
use echod_abstract::state::AState;
use echod_abstract::task_spec as tspec;
use echod_abstract::types as abs;
use echod_kernel::external as kext;
use echod_kernel::internal as kint;
use echod_kernel::properties as kprops;
use echod_kernel::steps as ksteps;
use echod_kernel::store::{object_order, AState as KState};
use echod_kernel::types as kernel;
use echod_kernel::types::{AOccurrence, ARequest, AResponse};

use crate::actions::*;
use crate::bridge::*;
use crate::fire_sim::*;
use crate::heartbeat_sim::*;
use crate::promise_sim::*;
use crate::read_sim::*;
use crate::relation::*;
use crate::schedule_sim::*;
use crate::suspend_sim::*;
use crate::sweep_sim::*;
use crate::task_sim::*;
use crate::*;

verus! {

// ---------------------------------------------------------------------------
// The Abstract's actions, as spec values
// ---------------------------------------------------------------------------

/// The Abstract's external actions the kernel's requests map to (its
/// searches have no kernel counterpart). A schedule create carries the
/// `nextCron` witness the Abstract action takes beside the request.
pub enum AbsExternal {
    PromiseGet(abs::APromiseGetReq),
    PromiseCreate(abs::APromiseCreateReq),
    PromiseSettle(abs::APromiseSettleReq),
    PromiseRegisterCallback(abs::APromiseRegisterCallbackReq),
    PromiseRegisterListener(abs::APromiseRegisterListenerReq),
    ScheduleGet(abs::AScheduleGetReq),
    ScheduleCreate(abs::AScheduleCreateReq, u64),
    ScheduleDelete(abs::AScheduleDeleteReq),
    TaskGet(abs::ATaskGetReq),
    TaskCreate(abs::ATaskCreateReq),
    TaskAcquire(abs::ATaskAcquireReq),
    TaskFulfill(abs::ATaskFulfillReq),
    TaskRelease(abs::ATaskReleaseReq),
    TaskHalt(abs::ATaskHaltReq),
    TaskContinue(abs::ATaskContinueReq),
    TaskFence(abs::ATaskFenceReq),
    TaskFenceCheck(abs::ATaskFenceCheckReq),
    TaskHeartbeat(abs::ATaskHeartbeatReq),
    TaskSuspend(abs::ATaskSuspendReq),
}

pub enum AbsResponse {
    Promise(abs::APromiseRes),
    Schedule(abs::AScheduleRes),
    ScheduleDelete(abs::AScheduleDeleteRes),
    Status(abs::AStatusRes),
    TaskGet(abs::ATaskGetRes),
    TaskClaim(abs::ATaskClaimRes),
    TaskFulfill(abs::ATaskFulfillRes),
    TaskSuspend(abs::ATaskSuspendRes),
    TaskFence(abs::ATaskFenceRes),
}

/// An Abstract external action at `now`, materializing: the state after and
/// the response, by the Abstract's own `spec_*_action`.
pub open spec fn external_step(a: AState, act: AbsExternal, now: u64) -> (AState, AbsResponse) {
    match act {
        AbsExternal::PromiseGet(q) => { let r = pspec::spec_promise_get_action(a, q, now, true); (r.next_state, AbsResponse::Promise(r.response)) }
        AbsExternal::PromiseCreate(q) => { let r = pspec::spec_promise_create_action(a, q, now, true); (r.next_state, AbsResponse::Promise(r.response)) }
        AbsExternal::PromiseSettle(q) => { let r = pspec::spec_promise_settle_action(a, q, now, true); (r.next_state, AbsResponse::Promise(r.response)) }
        AbsExternal::PromiseRegisterCallback(q) => { let r = pspec::spec_promise_register_callback_action(a, q, now, true); (r.next_state, AbsResponse::Promise(r.response)) }
        AbsExternal::PromiseRegisterListener(q) => { let r = pspec::spec_promise_register_listener_action(a, q, now, true); (r.next_state, AbsResponse::Promise(r.response)) }
        AbsExternal::ScheduleGet(q) => { let r = sspec::spec_schedule_get_action(a, q, now, true); (r.next_state, AbsResponse::Schedule(r.response)) }
        AbsExternal::ScheduleCreate(q, next) => { let r = sspec::spec_schedule_create_action(a, q, next, now, true); (r.next_state, AbsResponse::Schedule(r.response)) }
        AbsExternal::ScheduleDelete(q) => { let r = sspec::spec_schedule_delete_action(a, q, now, true); (r.next_state, AbsResponse::ScheduleDelete(r.response)) }
        AbsExternal::TaskGet(q) => { let r = tspec::spec_task_get_action(a, q, now, true); (r.next_state, AbsResponse::TaskGet(r.response)) }
        AbsExternal::TaskCreate(q) => { let r = tspec::spec_task_create_action(a, q, now, true); (r.next_state, AbsResponse::TaskClaim(r.response)) }
        AbsExternal::TaskAcquire(q) => { let r = tspec::spec_task_acquire_action(a, q, now, true); (r.next_state, AbsResponse::TaskClaim(r.response)) }
        AbsExternal::TaskFulfill(q) => { let r = tspec::spec_task_fulfill_action(a, q, now, true); (r.next_state, AbsResponse::TaskFulfill(r.response)) }
        AbsExternal::TaskRelease(q) => { let r = tspec::spec_task_release_action(a, q, now, true); (r.next_state, AbsResponse::Status(r.response)) }
        AbsExternal::TaskHalt(q) => { let r = tspec::spec_task_halt_action(a, q, now, true); (r.next_state, AbsResponse::Status(r.response)) }
        AbsExternal::TaskContinue(q) => { let r = tspec::spec_task_continue_action(a, q, now, true); (r.next_state, AbsResponse::Status(r.response)) }
        AbsExternal::TaskFence(q) => { let r = tspec::spec_task_fence_action(a, q, now, true); (r.next_state, AbsResponse::TaskFence(r.response)) }
        AbsExternal::TaskFenceCheck(q) => { let r = tspec::spec_task_fence_check_action(a, q, now, true); (r.next_state, AbsResponse::Status(r.response)) }
        AbsExternal::TaskHeartbeat(q) => { let r = tspec::spec_task_heartbeat_action(a, q, now, true); (r.next_state, AbsResponse::Status(r.response)) }
        AbsExternal::TaskSuspend(q) => { let r = tspec::spec_task_suspend_action(a, q, now, true); (r.next_state, AbsResponse::TaskSuspend(r.response)) }
    }
}

/// An Abstract action with the instant it runs at.
pub enum AbsAction {
    External(AbsExternal, u64),
    Internal(AbsInternal, u64),
}

pub open spec fn abs_step(a: AState, act: AbsAction, rt: u64) -> AState {
    match act {
        AbsAction::External(x, now) => external_step(a, x, now).0,
        AbsAction::Internal(x, now) => internal_step(a, x, now, rt),
    }
}

pub open spec fn abs_run(a: AState, acts: Seq<AbsAction>, rt: u64) -> AState
    decreases acts.len(),
{
    if acts.len() == 0 { a } else { abs_run(abs_step(a, acts[0], rt), acts.drop_first(), rt) }
}

/// The responses an Abstract run answers, in order; internal actions are
/// silent.
pub open spec fn abs_responses(a: AState, acts: Seq<AbsAction>, rt: u64) -> Seq<AbsResponse>
    decreases acts.len(),
{
    if acts.len() == 0 {
        Seq::empty()
    } else {
        let rest = abs_responses(abs_step(a, acts[0], rt), acts.drop_first(), rt);
        match acts[0] {
            AbsAction::External(x, now) => seq![external_step(a, x, now).1] + rest,
            AbsAction::Internal(_, _) => rest,
        }
    }
}

pub proof fn lemma_abs_run_app(a: AState, s: Seq<AbsAction>, t: Seq<AbsAction>, rt: u64)
    ensures
        abs_run(a, s + t, rt) == abs_run(abs_run(a, s, rt), t, rt),
        abs_responses(a, s + t, rt) == abs_responses(a, s, rt) + abs_responses(abs_run(a, s, rt), t, rt),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s + t =~= t);
        assert(abs_responses(a, s, rt) + abs_responses(a, t, rt) =~= abs_responses(a, t, rt));
    } else {
        assert((s + t)[0] == s[0]);
        assert((s + t).drop_first() =~= s.drop_first() + t);
        let a1 = abs_step(a, s[0], rt);
        lemma_abs_run_app(a1, s.drop_first(), t, rt);
        match s[0] {
            AbsAction::External(x, now) => {
                let r = seq![external_step(a, x, now).1];
                assert(r + (abs_responses(a1, s.drop_first(), rt) + abs_responses(abs_run(a, s, rt), t, rt))
                    =~= (r + abs_responses(a1, s.drop_first(), rt)) + abs_responses(abs_run(a, s, rt), t, rt));
            }
            AbsAction::Internal(_, _) => {}
        }
    }
}

pub proof fn lemma_abs_run_external_one(a: AState, x: AbsExternal, now: u64, rt: u64)
    ensures
        abs_run(a, seq![AbsAction::External(x, now)], rt) == external_step(a, x, now).0,
        abs_responses(a, seq![AbsAction::External(x, now)], rt) == seq![external_step(a, x, now).1],
{
    let act = AbsAction::External(x, now);
    let s = seq![act];
    assert(s.len() == 1 && s[0] == act);
    assert(s.drop_first() =~= Seq::<AbsAction>::empty());
    let a1 = abs_step(a, act, rt);
    assert(abs_run(a, s, rt) == abs_run(a1, s.drop_first(), rt));
    assert(abs_responses(a1, s.drop_first(), rt) =~= Seq::<AbsResponse>::empty());
    assert(abs_responses(a, s, rt) == seq![external_step(a, x, now).1] + abs_responses(a1, s.drop_first(), rt));
    assert(seq![external_step(a, x, now).1] + Seq::<AbsResponse>::empty() =~= seq![external_step(a, x, now).1]);
}

/// Internal actions at one instant, lifted.
pub open spec fn lift(s: Seq<AbsInternal>, now: u64) -> Seq<AbsAction> {
    s.map_values(|x: AbsInternal| AbsAction::Internal(x, now))
}

pub proof fn lemma_lift_run(a: AState, s: Seq<AbsInternal>, now: u64, rt: u64)
    ensures
        abs_run(a, lift(s, now), rt) == internal_run(a, s, now, rt),
        abs_responses(a, lift(s, now), rt) == Seq::<AbsResponse>::empty(),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(lift(s, now).len() == 0);
    } else {
        assert(lift(s, now)[0] == AbsAction::Internal(s[0], now));
        assert(lift(s, now).drop_first() =~= lift(s.drop_first(), now));
        lemma_lift_run(internal_step(a, s[0], now, rt), s.drop_first(), now, rt);
    }
}

// ---------------------------------------------------------------------------
// The kernel's requests and responses under the mapping
// ---------------------------------------------------------------------------

pub open spec fn request(req: ARequest) -> AbsExternal {
    match req {
        ARequest::PromiseGet(q) => AbsExternal::PromiseGet(promise_get_req(q)),
        ARequest::PromiseCreate(q) => AbsExternal::PromiseCreate(promise_create_req(q)),
        ARequest::PromiseSettle(q) => AbsExternal::PromiseSettle(promise_settle_req(q)),
        ARequest::PromiseRegisterCallback(q) => AbsExternal::PromiseRegisterCallback(promise_register_callback_req(q)),
        ARequest::PromiseRegisterListener(q) => AbsExternal::PromiseRegisterListener(promise_register_listener_req(q)),
        ARequest::ScheduleGet(q) => AbsExternal::ScheduleGet(schedule_get_req(q)),
        ARequest::ScheduleCreate(q) => AbsExternal::ScheduleCreate(schedule_create_req(q), q.next_run_at),
        ARequest::ScheduleDelete(q) => AbsExternal::ScheduleDelete(schedule_delete_req(q)),
        ARequest::TaskGet(q) => AbsExternal::TaskGet(task_get_req(q)),
        ARequest::TaskCreate(q) => AbsExternal::TaskCreate(task_create_req(q)),
        ARequest::TaskAcquire(q) => AbsExternal::TaskAcquire(task_acquire_req(q)),
        ARequest::TaskFulfill(q) => AbsExternal::TaskFulfill(task_fulfill_req(q)),
        ARequest::TaskRelease(q) => AbsExternal::TaskRelease(task_release_req(q)),
        ARequest::TaskHalt(q) => AbsExternal::TaskHalt(task_halt_req(q)),
        ARequest::TaskContinue(q) => AbsExternal::TaskContinue(task_continue_req(q)),
        ARequest::TaskFence(q) => AbsExternal::TaskFence(task_fence_req(q)),
        ARequest::TaskFenceCheck(q) => AbsExternal::TaskFenceCheck(task_fence_check_req(q)),
        ARequest::TaskHeartbeat(q) => AbsExternal::TaskHeartbeat(task_heartbeat_req(q)),
        ARequest::TaskSuspend(q) => AbsExternal::TaskSuspend(task_suspend_req(q)),
    }
}

/// The kernel's answer to `req`, as the Abstract's: the kernel answers a
/// status for several Abstract response kinds, so the request tells which.
pub open spec fn response(req: ARequest, res: AResponse) -> AbsResponse {
    match (req, res) {
        (ARequest::PromiseGet(_), AResponse::Promise(r)) => AbsResponse::Promise(promise_res(r)),
        (ARequest::PromiseCreate(_), AResponse::Promise(r)) => AbsResponse::Promise(promise_res(r)),
        (ARequest::PromiseSettle(_), AResponse::Promise(r)) => AbsResponse::Promise(promise_res(r)),
        (ARequest::PromiseRegisterCallback(_), AResponse::Promise(r)) => AbsResponse::Promise(promise_res(r)),
        (ARequest::PromiseRegisterListener(_), AResponse::Promise(r)) => AbsResponse::Promise(promise_res(r)),
        (ARequest::ScheduleGet(_), AResponse::Schedule(r)) => AbsResponse::Schedule(schedule_res(r)),
        (ARequest::ScheduleCreate(_), AResponse::Schedule(r)) => AbsResponse::Schedule(schedule_res(r)),
        (ARequest::ScheduleDelete(_), AResponse::Status(r)) => AbsResponse::ScheduleDelete(schedule_delete_res(r)),
        (ARequest::TaskGet(_), AResponse::TaskGet(r)) => AbsResponse::TaskGet(task_get_res(r)),
        (ARequest::TaskCreate(_), AResponse::TaskClaim(r)) => AbsResponse::TaskClaim(task_claim_res(r)),
        (ARequest::TaskAcquire(_), AResponse::TaskClaim(r)) => AbsResponse::TaskClaim(task_claim_res(r)),
        (ARequest::TaskFulfill(_), AResponse::Promise(r)) => AbsResponse::TaskFulfill(task_fulfill_res(r)),
        (ARequest::TaskRelease(_), AResponse::Status(r)) => AbsResponse::Status(status_res(r)),
        (ARequest::TaskHalt(_), AResponse::Status(r)) => AbsResponse::Status(status_res(r)),
        (ARequest::TaskContinue(_), AResponse::Status(r)) => AbsResponse::Status(status_res(r)),
        (ARequest::TaskFence(_), AResponse::TaskFence(r)) => AbsResponse::TaskFence(task_fence_res(r)),
        (ARequest::TaskFenceCheck(_), AResponse::Status(r)) => AbsResponse::Status(status_res(r)),
        (ARequest::TaskHeartbeat(_), AResponse::Status(r)) => AbsResponse::Status(status_res(r)),
        (ARequest::TaskSuspend(_), AResponse::Status(r)) => AbsResponse::TaskSuspend(task_suspend_res(r)),
        _ => arbitrary(),
    }
}

/// The door on a request: its ids canonical, its instants inside the time
/// door, its tags not a targeted timer; for the task handlers that count
/// versions, the document within the wire's bounds.
pub open spec fn request_in_domain(k: KState, req: ARequest, now: u64) -> bool {
    match req {
        ARequest::PromiseGet(q) => canonical(q.id),
        ARequest::PromiseCreate(q) => create_in_domain(q),
        ARequest::PromiseSettle(q) => canonical(q.id),
        ARequest::PromiseRegisterCallback(q) => canonical(q.awaited) && canonical(q.awaiter),
        ARequest::PromiseRegisterListener(q) => canonical(q.awaited),
        ARequest::ScheduleGet(q) => canonical(q.id),
        ARequest::ScheduleCreate(q) => schedule_create_in_domain(q, now),
        ARequest::ScheduleDelete(q) => canonical(q.id),
        ARequest::TaskGet(q) => doc_headroom(k) && canonical(q.id),
        ARequest::TaskCreate(q) => doc_headroom(k) && kprops::kernel_bounds(k) && create_in_domain(q.action) && q.ttl <= kernel::MAX_TIME && now <= kernel::MAX_TIME,
        ARequest::TaskAcquire(q) => doc_headroom(k) && canonical(q.id) && q.ttl <= kernel::MAX_TIME && now <= kernel::MAX_TIME,
        ARequest::TaskFulfill(q) => canonical(q.id),
        ARequest::TaskRelease(q) => canonical(q.id),
        ARequest::TaskHalt(q) => canonical(q.id),
        ARequest::TaskContinue(q) => canonical(q.id),
        ARequest::TaskFence(q) => fence_in_domain(q),
        ARequest::TaskFenceCheck(q) => canonical(q.id),
        ARequest::TaskHeartbeat(q) => kprops::kernel_bounds(k) && now <= kernel::MAX_TIME && canonical_refs(q.tasks),
        ARequest::TaskSuspend(q) => canonical(q.id) && canonical_actions(q.actions),
    }
}

/// What `lemma_handle_sim` says of one request.
pub open spec fn handle_simulates(k: KState, a: AState, req: ARequest, now: u64) -> bool {
    let (k2, res) = kext::spec_handle(k, req, now as nat);
    let (a2, ares) = external_step(a, request(req), now);
    &&& doc_related(k2, a2)
    &&& response(req, res) == ares
}

proof fn lemma_handle_promise(k: KState, a: AState, req: ARequest, now: u64)
    requires
        doc_related(k, a),
        request_in_domain(k, req, now),
        req is PromiseGet || req is PromiseCreate || req is PromiseSettle || req is PromiseRegisterCallback || req is PromiseRegisterListener,
    ensures handle_simulates(k, a, req, now),
{
    match req {
        ARequest::PromiseGet(q) => lemma_promise_get_sim(k, a, q, now),
        ARequest::PromiseCreate(q) => lemma_promise_create_sim(k, a, q, now),
        ARequest::PromiseSettle(q) => lemma_promise_settle_sim(k, a, q, now),
        ARequest::PromiseRegisterCallback(q) => lemma_promise_register_callback_sim(k, a, q, now),
        ARequest::PromiseRegisterListener(q) => lemma_promise_register_listener_sim(k, a, q, now),
        _ => {}
    }
}

proof fn lemma_handle_schedule(k: KState, a: AState, req: ARequest, now: u64)
    requires
        doc_related(k, a),
        request_in_domain(k, req, now),
        req is ScheduleGet || req is ScheduleCreate || req is ScheduleDelete,
    ensures handle_simulates(k, a, req, now),
{
    match req {
        ARequest::ScheduleGet(q) => lemma_schedule_get_sim(k, a, q, now),
        ARequest::ScheduleCreate(q) => lemma_schedule_create_sim(k, a, q, now),
        ARequest::ScheduleDelete(q) => lemma_schedule_delete_sim(k, a, q, now),
        _ => {}
    }
}

proof fn lemma_handle_task_claim(k: KState, a: AState, req: ARequest, now: u64)
    requires
        doc_related(k, a),
        request_in_domain(k, req, now),
        req is TaskGet || req is TaskCreate || req is TaskAcquire || req is TaskFulfill,
    ensures handle_simulates(k, a, req, now),
{
    match req {
        ARequest::TaskGet(q) => lemma_task_get_sim(k, a, q, now),
        ARequest::TaskCreate(q) => lemma_task_create_sim(k, a, q, now),
        ARequest::TaskAcquire(q) => lemma_task_acquire_sim(k, a, q, now),
        ARequest::TaskFulfill(q) => lemma_task_fulfill_sim(k, a, q, now),
        _ => {}
    }
}

proof fn lemma_handle_task_status(k: KState, a: AState, req: ARequest, now: u64)
    requires
        doc_related(k, a),
        request_in_domain(k, req, now),
        req is TaskRelease || req is TaskHalt || req is TaskContinue || req is TaskFenceCheck,
    ensures handle_simulates(k, a, req, now),
{
    match req {
        ARequest::TaskRelease(q) => lemma_task_release_sim(k, a, q, now),
        ARequest::TaskHalt(q) => lemma_task_halt_sim(k, a, q, now),
        ARequest::TaskContinue(q) => lemma_task_continue_sim(k, a, q, now),
        ARequest::TaskFenceCheck(q) => lemma_task_fence_check_sim(k, a, q, now),
        _ => {}
    }
}

proof fn lemma_handle_task_many(k: KState, a: AState, req: ARequest, now: u64)
    requires
        doc_related(k, a),
        request_in_domain(k, req, now),
        req is TaskFence || req is TaskHeartbeat || req is TaskSuspend,
    ensures handle_simulates(k, a, req, now),
{
    match req {
        ARequest::TaskFence(q) => lemma_task_fence_sim(k, a, q, now),
        ARequest::TaskHeartbeat(q) => lemma_task_heartbeat_sim(k, a, q, now),
        ARequest::TaskSuspend(q) => lemma_task_suspend_sim(k, a, q, now),
        _ => {}
    }
}

/// Every kernel handler simulates its Abstract action: the states stay
/// related and the responses agree.
pub proof fn lemma_handle_sim(k: KState, a: AState, req: ARequest, now: u64)
    requires doc_related(k, a), request_in_domain(k, req, now),
    ensures handle_simulates(k, a, req, now),
{
    match req {
        ARequest::PromiseGet(_) | ARequest::PromiseCreate(_) | ARequest::PromiseSettle(_)
        | ARequest::PromiseRegisterCallback(_) | ARequest::PromiseRegisterListener(_) => lemma_handle_promise(k, a, req, now),
        ARequest::ScheduleGet(_) | ARequest::ScheduleCreate(_) | ARequest::ScheduleDelete(_) => lemma_handle_schedule(k, a, req, now),
        ARequest::TaskGet(_) | ARequest::TaskCreate(_) | ARequest::TaskAcquire(_) | ARequest::TaskFulfill(_) => lemma_handle_task_claim(k, a, req, now),
        ARequest::TaskRelease(_) | ARequest::TaskHalt(_) | ARequest::TaskContinue(_) | ARequest::TaskFenceCheck(_) => lemma_handle_task_status(k, a, req, now),
        ARequest::TaskFence(_) | ARequest::TaskHeartbeat(_) | ARequest::TaskSuspend(_) => lemma_handle_task_many(k, a, req, now),
    }
}

// ---------------------------------------------------------------------------
// The Concrete document's steps
// ---------------------------------------------------------------------------

/// One kernel step on a document. `ids` is the stored row order the sweep
/// walks (`object_ids` of the store), a witness the step carries.
pub enum Micro {
    Sweep { now: u64, ids: Seq<Chars> },
    Handle { req: ARequest, now: u64 },
    Fire { sid: Chars, occs: Seq<AOccurrence>, next: u64, now: u64 },
}

/// The kernel's preconditions for the step, and the doors of the mapping.
pub open spec fn micro_ok(k: KState, m: Micro, rt: u64) -> bool {
    match m {
        Micro::Sweep { now, ids } => {
            &&& object_order(k, ids)
            &&& not_self(k)
            &&& now <= kernel::MAX_TIME
            &&& rt <= kernel::MAX_TIME
        }
        Micro::Handle { req, now } => request_in_domain(k, req, now),
        Micro::Fire { sid, occs, next, now } => {
            &&& canonical(sid)
            &&& canonical_occurrences(occs)
            &&& kprops::kernel_sched_bounds(k)
            &&& now <= kernel::MAX_TIME
            &&& forall|j: int| 0 <= j < occs.len() ==> #[trigger] occs[j].at <= now
            &&& forall|j: int, l: int| 0 <= j < l < occs.len() ==> #[trigger] occs[j].at < #[trigger] occs[l].at
            &&& occs.len() > 0 ==> next > occs[occs.len() - 1].at
            &&& k.schedules.contains_key(sid) && occs.len() > 0 ==> k.schedules[sid].next_run_at <= occs[0].at
        }
    }
}

pub open spec fn micro_step(k: KState, m: Micro, rt: u64) -> KState {
    match m {
        Micro::Sweep { now, ids } => ksteps::executable_single_pass(k, ids, now as nat, rt as nat),
        Micro::Handle { req, now } => kext::spec_handle(k, req, now as nat).0,
        Micro::Fire { sid, occs, next, now } => kint::spec_fire(k, sid, occs, next, now as nat),
    }
}

/// What the step answers, mapped: a handled request's response, else
/// nothing.
pub open spec fn micro_responses(k: KState, m: Micro) -> Seq<AbsResponse> {
    match m {
        Micro::Handle { req, now } => seq![response(req, kext::spec_handle(k, req, now as nat).1)],
        _ => Seq::empty(),
    }
}

/// The Abstract actions the step is.
pub open spec fn micro_actions(k: KState, m: Micro, rt: u64) -> Seq<AbsAction> {
    match m {
        Micro::Sweep { now, ids } => lift(sweep_actions(k, ids, now, rt), now),
        Micro::Handle { req, now } => seq![AbsAction::External(request(req), now)],
        Micro::Fire { sid, occs, next, now } => {
            if k.schedules.contains_key(sid) && occs.len() > 0 {
                let c = k.schedules[sid];
                let n = occs.len() as int;
                lift(fire_actions(k, sid, c, occs, now, n).push(AbsInternal::ScheduleAdvance(advance_req(sid, occs[n - 1], next))), now)
            } else {
                Seq::empty()
            }
        }
    }
}

/// The row order's ids are canonical: each is an object's id.
pub proof fn lemma_order_canonical(k: KState, a: AState, ids: Seq<Chars>)
    requires doc_related(k, a), object_order(k, ids),
    ensures canonical_ids(ids),
{
    assert forall|i: int| 0 <= i < ids.len() implies canonical(#[trigger] ids[i]) by {
        assert(k.objects.contains_key(ids[i]));
    }
}

/// One kernel step simulates its Abstract actions.
pub proof fn lemma_micro_sim(k: KState, a: AState, m: Micro, rt: u64)
    requires doc_related(k, a), micro_ok(k, m, rt),
    ensures
        doc_related(micro_step(k, m, rt), abs_run(a, micro_actions(k, m, rt), rt)),
        abs_responses(a, micro_actions(k, m, rt), rt) == micro_responses(k, m),
{
    match m {
        Micro::Sweep { now, ids } => {
            lemma_order_canonical(k, a, ids);
            lemma_sweep_sim(k, a, ids, now, rt);
            lemma_lift_run(a, sweep_actions(k, ids, now, rt), now, rt);
        }
        Micro::Handle { req, now } => {
            lemma_handle_sim(k, a, req, now);
            lemma_abs_run_external_one(a, request(req), now, rt);
        }
        Micro::Fire { sid, occs, next, now } => {
            if k.schedules.contains_key(sid) && occs.len() > 0 {
                let c = k.schedules[sid];
                let n = occs.len() as int;
                assert(occurrences_due(c, occs, now)) by {
                    assert forall|j: int| 0 <= j < occs.len() implies c.next_run_at <= #[trigger] occs[j].at && occs[j].at <= now by {
                        if j > 0 {
                            assert(occs[0].at < occs[j].at);
                        }
                    }
                }
                assert(kprops::kernel_sched_bounds_at(c));
                lemma_spec_fire_sim(k, a, sid, occs, next, now, rt);
                let acts = fire_actions(k, sid, c, occs, now, n).push(AbsInternal::ScheduleAdvance(advance_req(sid, occs[n - 1], next)));
                lemma_lift_run(a, acts, now, rt);
            } else {
                assert(kint::spec_fire(k, sid, occs, next, now as nat) == k);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Runs
// ---------------------------------------------------------------------------

pub open spec fn concrete_run(k: KState, ms: Seq<Micro>, rt: u64) -> KState
    decreases ms.len(),
{
    if ms.len() == 0 { k } else { concrete_run(micro_step(k, ms[0], rt), ms.drop_first(), rt) }
}

/// Every step admitted at the state it finds.
pub open spec fn concrete_ok(k: KState, ms: Seq<Micro>, rt: u64) -> bool
    decreases ms.len(),
{
    ms.len() == 0 || (micro_ok(k, ms[0], rt) && concrete_ok(micro_step(k, ms[0], rt), ms.drop_first(), rt))
}

pub open spec fn concrete_responses(k: KState, ms: Seq<Micro>, rt: u64) -> Seq<AbsResponse>
    decreases ms.len(),
{
    if ms.len() == 0 {
        Seq::empty()
    } else {
        micro_responses(k, ms[0]) + concrete_responses(micro_step(k, ms[0], rt), ms.drop_first(), rt)
    }
}

/// The Abstract run a Concrete run is.
pub open spec fn trace_actions(k: KState, ms: Seq<Micro>, rt: u64) -> Seq<AbsAction>
    decreases ms.len(),
{
    if ms.len() == 0 {
        Seq::empty()
    } else {
        micro_actions(k, ms[0], rt) + trace_actions(micro_step(k, ms[0], rt), ms.drop_first(), rt)
    }
}

/// Trace inclusion. From related states, every admitted Concrete run has an
/// Abstract run, `trace_actions`, that ends related to it and answers the
/// same responses in the same order.
pub proof fn theorem_trace_inclusion(k: KState, a: AState, ms: Seq<Micro>, rt: u64)
    requires doc_related(k, a), concrete_ok(k, ms, rt),
    ensures
        doc_related(concrete_run(k, ms, rt), abs_run(a, trace_actions(k, ms, rt), rt)),
        abs_responses(a, trace_actions(k, ms, rt), rt) == concrete_responses(k, ms, rt),
    decreases ms.len(),
{
    if ms.len() == 0 {
    } else {
        let m = ms[0];
        lemma_micro_sim(k, a, m, rt);
        let k1 = micro_step(k, m, rt);
        let acts = micro_actions(k, m, rt);
        let a1 = abs_run(a, acts, rt);
        theorem_trace_inclusion(k1, a1, ms.drop_first(), rt);
        lemma_abs_run_app(a, acts, trace_actions(k1, ms.drop_first(), rt), rt);
    }
}

/// The empty document: the kernel's `empty_doc`, as a state.
pub open spec fn kernel_init() -> KState {
    ksteps::full(ksteps::empty_doc())
}

pub proof fn lemma_init_doc_related()
    ensures doc_related(kernel_init(), abstract_init()),
{
}

/// The same, from the initial states: the empty document and the Abstract's
/// empty state.
pub proof fn theorem_trace_inclusion_from_init(ms: Seq<Micro>, rt: u64)
    requires concrete_ok(kernel_init(), ms, rt),
    ensures
        doc_related(concrete_run(kernel_init(), ms, rt), abs_run(abstract_init(), trace_actions(kernel_init(), ms, rt), rt)),
        abs_responses(abstract_init(), trace_actions(kernel_init(), ms, rt), rt) == concrete_responses(kernel_init(), ms, rt),
{
    lemma_init_doc_related();
    theorem_trace_inclusion(kernel_init(), abstract_init(), ms, rt);
}

} // verus!
