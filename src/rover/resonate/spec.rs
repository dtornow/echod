//! The functional specification of the model: what each request and each piece
//! of internal work does, as spec functions over the state's view. These are
//! the `spec_external` and `spec_internal` twins the trace semantics
//! (`accordant::semantics`) is stated over, so `valid(Resonate, ..)` says
//! something definite, and a refinement theorem has a side to land on.
//!
//! The executable handlers (`exec.rs`) are the same protocol written to run,
//! and each is verified to compute its twin here (its `ensures`). The `Model`
//! impl at the end is verified too: so the checker's verdicts, which speak
//! about the code, speak about these twins, with nothing in between.
//!
//! Views: ids and strings as `Seq<char>`, the persistent maps as `Map`, the
//! sets as `Set`. A value of the model's own types with a given view is
//! obtained by `choose`; that every view is realised by some value is the one
//! axiom this module adds (`axiom_realised`), true of the types as built; that
//! a value is its view (`collections.rs`) makes the choice the value itself.

// Outside Verus (`cargo build`) the spec functions and proofs are erased, and
// the imports they use with them.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use crate::semantics::{ExternalOutcomeV, InternalOutcomeV};
use crate::{ExternalOutcome, InternalOutcome, Model, Sched};

use super::collections::*;
use super::exec::*;

verus! {

// ------------------------------------------------------------------- views

pub type Chars = Seq<char>;

pub struct PromiseV {
    pub state: PState,
    pub value: Option<Chars>,
    pub param: Option<Chars>,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub tags: Tags,
    pub callbacks: Set<Chars>,
    pub listeners: Set<Chars>,
}

pub struct TaskV {
    pub state: TState,
    pub version: u32,
    pub pid: Option<Chars>,
    pub ttl: Option<Time>,
    pub acquired_at: Time,
    pub retry_at: Option<Time>,
    pub resumes: Seq<Chars>,
}

pub struct ScheduleV {
    pub id: Chars,
    pub cron: Chars,
    pub promise_id: Chars,
    pub promise_timeout: Time,
    pub promise_param: Option<Chars>,
    pub promise_tags: Tags,
    pub created_at: Time,
    pub next_run_at: Time,
    pub last_run_at: Option<Time>,
}

pub struct ServerV {
    pub promises: Map<Chars, PromiseV>,
    pub tasks: Map<Chars, TaskV>,
    pub schedules: Map<Chars, ScheduleV>,
}

pub struct CreateV {
    pub id: Chars,
    pub timeout_at: Time,
    pub data: Option<Chars>,
    pub tags: Tags,
}

pub struct SettleV {
    pub id: Chars,
    pub state: Chars,
    pub data: Option<Chars>,
}

pub enum FencedV {
    Create(CreateV),
    Settle(SettleV),
}

pub struct TaskRefV {
    pub id: Chars,
    pub version: u32,
}

pub struct ScheduleCreateV {
    pub id: Chars,
    pub cron: Chars,
    pub promise_id: Chars,
    pub promise_timeout: Time,
    pub promise_param: Option<Chars>,
    pub promise_tags: Tags,
}

pub enum RequestV {
    CreatePromise(CreateV),
    GetPromise(Chars),
    SettlePromise(SettleV),
    RegisterCallback { awaited: Chars, awaiter: Chars },
    RegisterListener { awaited: Chars, address: Chars },
    GetTask(Chars),
    CreateTask { pid: Chars, ttl: Time, action: CreateV },
    AcquireTask { id: Chars, version: u32, pid: Chars, ttl: Time },
    ReleaseTask { id: Chars, version: u32 },
    FulfillTask { id: Chars, version: u32, state: Chars, data: Option<Chars> },
    HeartbeatTask { pid: Chars, tasks: Seq<TaskRefV> },
    SuspendTask { id: Chars, version: u32, awaited: Seq<Chars> },
    FenceTask { id: Chars, version: u32, action: FencedV },
    HaltTask(Chars),
    ContinueTask(Chars),
    CreateSchedule(ScheduleCreateV),
    GetSchedule(Chars),
    DeleteSchedule(Chars),
}

pub struct PromiseRecV {
    pub id: Chars,
    pub state: PState,
    pub param: Option<Chars>,
    pub value: Option<Chars>,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub tags: Tags,
}

pub struct TaskRecV {
    pub id: Chars,
    pub state: TState,
    pub version: u32,
    pub pid: Option<Chars>,
    pub ttl: Option<Time>,
    pub resumes: u32,
}

pub enum ResponseV {
    Status(u16),
    Promise(PromiseRecV),
    Task(TaskRecV),
    Both(PromiseRecV, TaskRecV),
    Schedule(ScheduleV),
}

pub enum DispatchV {
    Execute { id: Chars, version: u32 },
    Unblock { address: Chars, promise: PromiseRecV },
}

pub enum InternalV {
    On(Seq<Chars>),
    Fire { schedule: Chars, at: Time, promise: Chars },
    Advance { schedule: Chars, at: Time, promise: Chars },
}

pub open spec fn ostr(o: Option<String>) -> Option<Chars> {
    match o {
        Some(s) => Some(s@),
        None => None,
    }
}

pub open spec fn strs(v: Seq<String>) -> Seq<Chars> {
    v.map_values(|s: String| s@)
}

impl View for Promise {
    type V = PromiseV;

    open spec fn view(&self) -> PromiseV {
        PromiseV {
            state: self.state,
            value: ostr(self.value),
            param: ostr(self.param),
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
            tags: self.tags,
            callbacks: self.callbacks@,
            listeners: self.listeners@,
        }
    }
}

impl View for Task {
    type V = TaskV;

    open spec fn view(&self) -> TaskV {
        TaskV {
            state: self.state,
            version: self.version,
            pid: ostr(self.pid),
            ttl: self.ttl,
            acquired_at: self.acquired_at,
            retry_at: self.retry_at,
            resumes: strs(self.resumes@),
        }
    }
}

impl View for Schedule {
    type V = ScheduleV;

    open spec fn view(&self) -> ScheduleV {
        ScheduleV {
            id: self.id@,
            cron: self.cron@,
            promise_id: self.promise_id@,
            promise_timeout: self.promise_timeout,
            promise_param: ostr(self.promise_param),
            promise_tags: self.promise_tags,
            created_at: self.created_at,
            next_run_at: self.next_run_at,
            last_run_at: self.last_run_at,
        }
    }
}

impl View for Server {
    type V = ServerV;

    open spec fn view(&self) -> ServerV {
        ServerV {
            promises: self.promises@.map_values(|p: Promise| p@),
            tasks: self.tasks@.map_values(|t: Task| t@),
            schedules: self.schedules@.map_values(|c: Schedule| c@),
        }
    }
}

impl View for Create {
    type V = CreateV;

    open spec fn view(&self) -> CreateV {
        CreateV { id: self.id@, timeout_at: self.timeout_at, data: ostr(self.data), tags: self.tags }
    }
}

impl View for Settle {
    type V = SettleV;

    open spec fn view(&self) -> SettleV {
        SettleV { id: self.id@, state: self.state@, data: ostr(self.data) }
    }
}

impl View for Fenced {
    type V = FencedV;

    open spec fn view(&self) -> FencedV {
        match self {
            Fenced::Create(c) => FencedV::Create(c@),
            Fenced::Settle(s) => FencedV::Settle(s@),
        }
    }
}

impl View for TaskRef {
    type V = TaskRefV;

    open spec fn view(&self) -> TaskRefV {
        TaskRefV { id: self.id@, version: self.version }
    }
}

impl View for ScheduleCreate {
    type V = ScheduleCreateV;

    open spec fn view(&self) -> ScheduleCreateV {
        ScheduleCreateV {
            id: self.id@,
            cron: self.cron@,
            promise_id: self.promise_id@,
            promise_timeout: self.promise_timeout,
            promise_param: ostr(self.promise_param),
            promise_tags: self.promise_tags,
        }
    }
}

impl View for Request {
    type V = RequestV;

    open spec fn view(&self) -> RequestV {
        match self {
            Request::CreatePromise(c) => RequestV::CreatePromise(c@),
            Request::GetPromise(id) => RequestV::GetPromise(id@),
            Request::SettlePromise(s) => RequestV::SettlePromise(s@),
            Request::RegisterCallback { awaited, awaiter } => RequestV::RegisterCallback { awaited: awaited@, awaiter: awaiter@ },
            Request::RegisterListener { awaited, address } => RequestV::RegisterListener { awaited: awaited@, address: address@ },
            Request::GetTask(id) => RequestV::GetTask(id@),
            Request::CreateTask { pid, ttl, action } => RequestV::CreateTask { pid: pid@, ttl: *ttl, action: action@ },
            Request::AcquireTask { id, version, pid, ttl } => RequestV::AcquireTask { id: id@, version: *version, pid: pid@, ttl: *ttl },
            Request::ReleaseTask { id, version } => RequestV::ReleaseTask { id: id@, version: *version },
            Request::FulfillTask { id, version, state, data } => RequestV::FulfillTask { id: id@, version: *version, state: state@, data: ostr(*data) },
            Request::HeartbeatTask { pid, tasks } => RequestV::HeartbeatTask { pid: pid@, tasks: tasks@.map_values(|r: TaskRef| r@) },
            Request::SuspendTask { id, version, awaited } => RequestV::SuspendTask { id: id@, version: *version, awaited: strs(awaited@) },
            Request::FenceTask { id, version, action } => RequestV::FenceTask { id: id@, version: *version, action: action@ },
            Request::HaltTask(id) => RequestV::HaltTask(id@),
            Request::ContinueTask(id) => RequestV::ContinueTask(id@),
            Request::CreateSchedule(c) => RequestV::CreateSchedule(c@),
            Request::GetSchedule(id) => RequestV::GetSchedule(id@),
            Request::DeleteSchedule(id) => RequestV::DeleteSchedule(id@),
        }
    }
}

impl View for PromiseRec {
    type V = PromiseRecV;

    open spec fn view(&self) -> PromiseRecV {
        PromiseRecV {
            id: self.id@,
            state: self.state,
            param: ostr(self.param),
            value: ostr(self.value),
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
            tags: self.tags,
        }
    }
}

impl View for TaskRec {
    type V = TaskRecV;

    open spec fn view(&self) -> TaskRecV {
        TaskRecV { id: self.id@, state: self.state, version: self.version, pid: ostr(self.pid), ttl: self.ttl, resumes: self.resumes }
    }
}

impl View for Response {
    type V = ResponseV;

    open spec fn view(&self) -> ResponseV {
        match self {
            Response::Status(c) => ResponseV::Status(*c),
            Response::Promise(p) => ResponseV::Promise(p@),
            Response::Task(t) => ResponseV::Task(t@),
            Response::Both(p, t) => ResponseV::Both(p@, t@),
            Response::Schedule(c) => ResponseV::Schedule(c@),
        }
    }
}

impl View for Dispatch {
    type V = DispatchV;

    open spec fn view(&self) -> DispatchV {
        match self {
            Dispatch::Execute { id, version } => DispatchV::Execute { id: id@, version: *version },
            Dispatch::Unblock { address, promise } => DispatchV::Unblock { address: address@, promise: promise@ },
        }
    }
}

impl View for Internal {
    type V = InternalV;

    open spec fn view(&self) -> InternalV {
        match self {
            Internal::On(ids) => InternalV::On(strs(ids@)),
            Internal::Fire { schedule, at, promise } => InternalV::Fire { schedule: schedule@, at: *at, promise: promise@ },
            Internal::Advance { schedule, at, promise } => InternalV::Advance { schedule: schedule@, at: *at, promise: promise@ },
        }
    }
}

impl View for Step {
    type V = InternalV;

    open spec fn view(&self) -> InternalV {
        match self {
            Step::Objects(ids) => InternalV::On(strs(ids@)),
            Step::Fire { schedule, at, promise } => InternalV::Fire { schedule: schedule@, at: *at, promise: promise@ },
            Step::Advance { schedule, at, promise } => InternalV::Advance { schedule: schedule@, at: *at, promise: promise@ },
        }
    }
}

impl View for Work {
    type V = Sched<InternalV>;

    open spec fn view(&self) -> Sched<InternalV> {
        match self {
            Work::Later(s) => Sched::Later(s@),
            Work::Timer(t, s) => Sched::Timer(*t, s@),
        }
    }
}

/// An internal item of the checker's, as a view.
pub open spec fn sched_v(s: Sched<Internal>) -> Sched<InternalV> {
    match s {
        Sched::Later(r) => Sched::Later(r@),
        Sched::Timer(t, r) => Sched::Timer(t, r@),
    }
}

pub open spec fn works(v: Seq<Work>) -> Seq<Sched<InternalV>> {
    v.map_values(|w: Work| w@)
}

pub open spec fn sends(v: Seq<Dispatch>) -> Seq<DispatchV> {
    v.map_values(|d: Dispatch| d@)
}

// ------------------------------------------------------------------ outcomes

pub struct OutV {
    pub resp: ResponseV,
    pub next: ServerV,
    pub work: Seq<Sched<InternalV>>,
    pub send: Seq<DispatchV>,
}

pub struct InOutV {
    pub next: ServerV,
    pub work: Seq<Sched<InternalV>>,
    pub send: Seq<DispatchV>,
    pub pending: bool,
}

impl View for Out {
    type V = OutV;

    open spec fn view(&self) -> OutV {
        OutV { resp: self.resp@, next: self.next@, work: works(self.work@), send: sends(self.send@) }
    }
}

impl View for InOut {
    type V = InOutV;

    open spec fn view(&self) -> InOutV {
        InOutV { next: self.next@, work: works(self.work@), send: sends(self.send@), pending: self.pending }
    }
}

pub open spec fn outs_v(v: Seq<Out>) -> Seq<OutV> {
    v.map_values(|o: Out| o@)
}

// ------------------------------------------------------- views, under maps

pub broadcast proof fn lemma_mv_empty<A, B>(f: spec_fn(A) -> B)
    ensures
        #[trigger] Seq::<A>::empty().map_values(f) == Seq::<B>::empty(),
{
    assert(Seq::<A>::empty().map_values(f) =~= Seq::<B>::empty());
}

pub broadcast proof fn lemma_mv_push<A, B>(v: Seq<A>, x: A, f: spec_fn(A) -> B)
    ensures
        #[trigger] v.push(x).map_values(f) == v.map_values(f).push(f(x)),
{
    assert(v.push(x).map_values(f) =~= v.map_values(f).push(f(x)));
}

pub broadcast proof fn lemma_mv_add<A, B>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> B)
    ensures
        #[trigger] (a + b).map_values(f) == a.map_values(f) + b.map_values(f),
{
    assert((a + b).map_values(f) =~= a.map_values(f) + b.map_values(f));
}

pub broadcast proof fn lemma_mv_take<A, B>(v: Seq<A>, i: int, f: spec_fn(A) -> B)
    requires
        0 <= i <= v.len(),
    ensures
        #[trigger] v.take(i).map_values(f) == v.map_values(f).take(i),
{
    assert(v.take(i).map_values(f) =~= v.map_values(f).take(i));
}

pub broadcast proof fn lemma_map_values_insert<A, B>(m: Map<Chars, A>, k: Chars, v: A, f: spec_fn(A) -> B)
    ensures
        #[trigger] m.insert(k, v).map_values(f) == m.map_values(f).insert(k, f(v)),
{
    assert(m.insert(k, v).map_values(f) =~= m.map_values(f).insert(k, f(v)));
}

pub broadcast proof fn lemma_map_values_remove<A, B>(m: Map<Chars, A>, k: Chars, f: spec_fn(A) -> B)
    ensures
        #[trigger] m.remove(k).map_values(f) == m.map_values(f).remove(k),
{
    assert(m.remove(k).map_values(f) =~= m.map_values(f).remove(k));
}

pub broadcast proof fn lemma_strs_len(v: Seq<String>)
    ensures
        #[trigger] strs(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_strs_index(v: Seq<String>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] strs(v)[i] == v[i]@,
{
}

pub broadcast proof fn lemma_works_len(v: Seq<Work>)
    ensures
        #[trigger] works(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_works_index(v: Seq<Work>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] works(v)[i] == v[i]@,
{
}

pub broadcast proof fn lemma_sends_len(v: Seq<Dispatch>)
    ensures
        #[trigger] sends(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_sends_index(v: Seq<Dispatch>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] sends(v)[i] == v[i]@,
{
}

pub broadcast proof fn lemma_outs_len(v: Seq<Out>)
    ensures
        #[trigger] outs_v(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_outs_index(v: Seq<Out>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] outs_v(v)[i] == v[i]@,
{
}

pub broadcast group group_views {
    lemma_strs_len,
    lemma_strs_index,
    lemma_works_len,
    lemma_works_index,
    lemma_sends_len,
    lemma_sends_index,
    lemma_outs_len,
    lemma_outs_index,
    lemma_mv_empty,
    lemma_mv_push,
    lemma_mv_add,
    lemma_mv_take,
    lemma_map_values_insert,
    lemma_map_values_remove,
    axiom_pset_seq,
}

pub open spec fn sat_add(a: Time, b: Time) -> Time {
    if a + b > u64::MAX { u64::MAX } else { (a + b) as Time }
}

pub open spec fn sat_mul(a: Time, b: Time) -> Time {
    if a * b > u64::MAX { u64::MAX } else { (a * b) as Time }
}

/// The last version a task can take: an acquire at it is refused (409), as
/// the servers refuse one at their own door.
pub const MAX_VERSION: u32 = u32::MAX;

pub open spec fn status_v(code: u16, s: ServerV) -> Seq<OutV> {
    seq![OutV { resp: ResponseV::Status(code), next: s, work: Seq::empty(), send: Seq::empty() }]
}

pub open spec fn echo_v(res: ResponseV, s: ServerV) -> Seq<OutV> {
    seq![OutV { resp: res, next: s, work: Seq::empty(), send: Seq::empty() }]
}

pub open spec fn one_v(resp: ResponseV, next: ServerV, work: Seq<Sched<InternalV>>, send: Seq<DispatchV>) -> Seq<OutV> {
    seq![OutV { resp, next, work, send }]
}

/// Work on one object at `at`.
pub open spec fn at_v(t: Time, id: Chars) -> Sched<InternalV> {
    Sched::Timer(t, InternalV::On(seq![id]))
}

pub open spec fn later2_v(a: Chars, b: Chars) -> Sched<InternalV> {
    Sched::Later(InternalV::On(seq![a, b]))
}

pub open spec fn external_v(p: PromiseV) -> bool {
    p.tags.target || p.tags.external || p.tags.timer
}

pub open spec fn live_v(p: PromiseV) -> bool {
    p.state == PState::Pending
}

pub open spec fn prec_v(id: Chars, p: PromiseV) -> PromiseRecV {
    PromiseRecV {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
        tags: p.tags,
    }
}

pub open spec fn trec_v(id: Chars, t: TaskV) -> TaskRecV {
    let resumes: u32 = if t.resumes.len() > u32::MAX { u32::MAX } else { t.resumes.len() as u32 };
    TaskRecV { id, state: t.state, version: t.version, pid: t.pid, ttl: t.ttl, resumes }
}

/// Done: the lease and the offer gone, with the lease's start. (The lease's
/// start lives only while the task is held.)
pub open spec fn fulfilled_v(t: TaskV) -> TaskV {
    TaskV { state: TState::Fulfilled, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty(), ..t }
}

pub open spec fn acquired_v(t: TaskV, version: u32, pid: Chars, ttl: Time, now: Time) -> TaskV {
    TaskV { state: TState::Acquired, version, pid: Some(pid), ttl: Some(ttl), acquired_at: now, retry_at: None, resumes: Seq::empty(), ..t }
}

/// Back to pending, to be offered again at `at`.
pub open spec fn released_v(t: TaskV, at: Time) -> TaskV {
    TaskV { state: TState::Pending, pid: None, ttl: None, acquired_at: 0, retry_at: Some(at), ..t }
}

pub open spec fn lease_expires_v(t: TaskV) -> Time {
    match t.ttl {
        Some(ttl) => sat_add(t.acquired_at, ttl),
        None => t.acquired_at,
    }
}

/// Lean's `nextOffer`: the first instant on the grid `due + k·T` strictly
/// after `now`. `T = 0` is treated as 1.
pub open spec fn next_offer_v(due: Time, now: Time, t0: Time) -> Time {
    let t: Time = if t0 == 0 { 1 } else { t0 };
    if now < due {
        due
    } else {
        let k: Time = ((now - due) / (t as int)) as Time;
        sat_add(due, sat_mul(t, sat_add(k, 1)))
    }
}

/// Settles `id` and fulfills its task, if any.
pub open spec fn settle_v(s: ServerV, id: Chars, state: PState, value: Option<Chars>, at: Time) -> ServerV {
    let promises = if s.promises.contains_key(id) {
        let p = s.promises[id];
        s.promises.insert(id, PromiseV { state, value, settled_at: Some(at), ..p })
    } else {
        s.promises
    };
    let tasks = if s.tasks.contains_key(id) && s.tasks[id].state != TState::Fulfilled {
        s.tasks.insert(id, fulfilled_v(s.tasks[id]))
    } else {
        s.tasks
    };
    ServerV { promises, tasks, ..s }
}

/// The work a settled promise starts: one resume per stored callback, and its
/// listeners' unblocks.
pub open spec fn settled_work_v(p: PromiseV, awaited: Chars) -> Seq<Sched<InternalV>> {
    let resumes = pset_seq(p.callbacks).map_values(|w: Chars| later2_v(awaited, w));
    if p.listeners.len() > 0 {
        resumes.push(Sched::Later(InternalV::On(seq![awaited])))
    } else {
        resumes
    }
}

/// The checks every task.* mutation shares: exists, acquired, own promise live,
/// version matches.
pub open spec fn held_v(s: ServerV, id: Chars, version: u32) -> Result<TaskV, u16> {
    if !s.tasks.contains_key(id) {
        Err(404)
    } else {
        let t = s.tasks[id];
        let live = s.promises.contains_key(id) && live_v(s.promises[id]);
        if t.state != TState::Acquired || !live || t.version != version {
            Err(409)
        } else {
            Ok(t)
        }
    }
}

// ------------------------------------------------------------------ handlers

pub open spec fn promise_create_v(req: CreateV, s: ServerV, now: Time) -> Seq<OutV> {
    if req.tags.timer && req.tags.target {
        status_v(400, s)
    } else if req.tags.delay is Some && req.tags.delay.unwrap() >= req.timeout_at {
        status_v(400, s)
    } else if req.tags.delay is Some && !req.tags.target {
        status_v(400, s)
    } else if s.promises.contains_key(req.id) {
        echo_v(ResponseV::Promise(prec_v(req.id, s.promises[req.id])), s)
    } else {
        let live = req.timeout_at > now;
        let born = if live { PState::Pending } else if req.tags.timer { PState::Resolved } else { PState::TimedOut };
        let p = PromiseV {
            state: born,
            value: None,
            param: req.data,
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: req.tags,
            callbacks: Set::empty(),
            listeners: Set::empty(),
        };
        let work0: Seq<Sched<InternalV>> = if live { seq![at_v(req.timeout_at, req.id)] } else { Seq::empty() };
        let promises = s.promises.insert(req.id, p);
        if req.tags.target {
            let due = match req.tags.delay {
                Some(d) => if d > now { d } else { now },
                None => now,
            };
            let task = TaskV {
                state: if live { TState::Pending } else { TState::Fulfilled },
                version: 0,
                pid: None,
                ttl: None,
                acquired_at: 0,
                retry_at: if live { Some(due) } else { None },
                resumes: Seq::empty(),
            };
            let work = if live { work0.push(at_v(due, req.id)) } else { work0 };
            one_v(ResponseV::Promise(prec_v(req.id, p)), ServerV { promises, tasks: s.tasks.insert(req.id, task), ..s }, work, Seq::empty())
        } else {
            one_v(ResponseV::Promise(prec_v(req.id, p)), ServerV { promises, ..s }, work0, Seq::empty())
        }
    }
}

pub open spec fn promise_settle_v(req: SettleV, s: ServerV, now: Time) -> Seq<OutV> {
    match spec_settable(req.state) {
        None => status_v(400, s),
        Some(state) => {
            if !s.promises.contains_key(req.id) {
                status_v(404, s)
            } else {
                let p = s.promises[req.id];
                if !live_v(p) {
                    echo_v(ResponseV::Promise(prec_v(req.id, p)), s)
                } else {
                    let work = settled_work_v(p, req.id);
                    let n = settle_v(s, req.id, state, req.data, now);
                    one_v(ResponseV::Promise(prec_v(req.id, n.promises[req.id])), n, work, Seq::empty())
                }
            }
        },
    }
}

pub open spec fn promise_register_callback_v(awaited: Chars, awaiter: Chars, s: ServerV) -> Seq<OutV> {
    if awaited == awaiter || origin(awaited) != origin(awaiter) {
        status_v(400, s)
    } else if !s.promises.contains_key(awaited) {
        status_v(404, s)
    } else if !s.promises.contains_key(awaiter) {
        status_v(422, s)
    } else {
        let p = s.promises[awaited];
        let w = s.promises[awaiter];
        if !s.tasks.contains_key(awaiter) || !external_v(p) {
            status_v(422, s)
        } else {
            let res = ResponseV::Promise(prec_v(awaited, p));
            if !live_v(p) || !live_v(w) {
                echo_v(res, s)
            } else {
                let q = PromiseV { callbacks: p.callbacks.insert(awaiter), ..p };
                one_v(res, ServerV { promises: s.promises.insert(awaited, q), ..s }, Seq::empty(), Seq::empty())
            }
        }
    }
}

pub open spec fn promise_register_listener_v(awaited: Chars, address: Chars, s: ServerV) -> Seq<OutV> {
    if !spec_address_valid(address) {
        status_v(400, s)
    } else if !s.promises.contains_key(awaited) {
        status_v(404, s)
    } else {
        let p = s.promises[awaited];
        if !external_v(p) {
            status_v(422, s)
        } else {
            let res = ResponseV::Promise(prec_v(awaited, p));
            if !live_v(p) {
                echo_v(res, s)
            } else {
                let q = PromiseV { listeners: p.listeners.insert(address), ..p };
                one_v(res, ServerV { promises: s.promises.insert(awaited, q), ..s }, Seq::empty(), Seq::empty())
            }
        }
    }
}

pub open spec fn task_create_v(pid: Chars, ttl: Time, req: CreateV, s: ServerV, now: Time) -> Seq<OutV> {
    if !req.tags.target || req.tags.timer {
        status_v(400, s)
    } else if req.tags.delay is Some {
        status_v(400, s)
    } else if s.promises.contains_key(req.id) {
        let p = s.promises[req.id];
        if !p.tags.target {
            status_v(422, s)
        } else if !s.tasks.contains_key(req.id) {
            status_v(409, s)
        } else {
            let t = s.tasks[req.id];
            match t.state {
                TState::Fulfilled => echo_v(ResponseV::Both(prec_v(req.id, p), trec_v(req.id, t)), s),
                TState::Pending => if t.version >= MAX_VERSION {
                    status_v(409, s)
                } else {
                    let u = acquired_v(t, (t.version + 1) as u32, pid, ttl, now);
                    one_v(
                        ResponseV::Both(prec_v(req.id, p), trec_v(req.id, u)),
                        ServerV { tasks: s.tasks.insert(req.id, u), ..s },
                        seq![at_v(sat_add(now, ttl), req.id)],
                        Seq::empty(),
                    )
                },
                _ => status_v(409, s),
            }
        }
    } else {
        let live = req.timeout_at > now;
        let p = PromiseV {
            state: if live { PState::Pending } else { PState::TimedOut },
            value: None,
            param: req.data,
            timeout_at: req.timeout_at,
            created_at: if live { now } else { req.timeout_at },
            settled_at: if live { None } else { Some(req.timeout_at) },
            tags: req.tags,
            callbacks: Set::empty(),
            listeners: Set::empty(),
        };
        let t0 = TaskV { state: TState::Fulfilled, version: 0, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty() };
        let t = if live { acquired_v(t0, 1, pid, ttl, now) } else { t0 };
        let work: Seq<Sched<InternalV>> = if live { seq![at_v(req.timeout_at, req.id), at_v(sat_add(now, ttl), req.id)] } else { Seq::empty() };
        one_v(
            ResponseV::Both(prec_v(req.id, p), trec_v(req.id, t)),
            ServerV { promises: s.promises.insert(req.id, p), tasks: s.tasks.insert(req.id, t), ..s },
            work,
            Seq::empty(),
        )
    }
}

pub open spec fn task_acquire_v(id: Chars, version: u32, pid: Chars, ttl: Time, s: ServerV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id) {
        status_v(404, s)
    } else if !s.promises.contains_key(id) {
        status_v(404, s)
    } else {
        let t = s.tasks[id];
        let p = s.promises[id];
        if t.state != TState::Pending || !live_v(p) || t.version != version || t.version >= MAX_VERSION {
            status_v(409, s)
        } else {
            let u = acquired_v(t, (t.version + 1) as u32, pid, ttl, now);
            one_v(
                ResponseV::Both(prec_v(id, p), trec_v(id, u)),
                ServerV { tasks: s.tasks.insert(id, u), ..s },
                seq![at_v(sat_add(now, ttl), id)],
                Seq::empty(),
            )
        }
    }
}

pub open spec fn task_release_v(id: Chars, version: u32, s: ServerV, now: Time) -> Seq<OutV> {
    match held_v(s, id, version) {
        Err(code) => status_v(code, s),
        Ok(t) => one_v(
            ResponseV::Status(200),
            ServerV { tasks: s.tasks.insert(id, released_v(t, now)), ..s },
            seq![at_v(now, id)],
            Seq::empty(),
        ),
    }
}

pub open spec fn task_fulfill_v(id: Chars, version: u32, state: Chars, data: Option<Chars>, s: ServerV, now: Time) -> Seq<OutV> {
    match spec_settable(state) {
        None => status_v(400, s),
        Some(st) => match held_v(s, id, version) {
            Err(code) => status_v(code, s),
            Ok(_) => {
                let work = if s.promises.contains_key(id) { settled_work_v(s.promises[id], id) } else { Seq::empty() };
                let n = settle_v(s, id, st, data, now);
                let res = if n.promises.contains_key(id) { ResponseV::Promise(prec_v(id, n.promises[id])) } else { ResponseV::Status(500) };
                one_v(res, n, work, Seq::empty())
            },
        },
    }
}

/// Every task after the first is in the first's origin.
pub open spec fn one_origin(refs: Seq<TaskRefV>) -> bool {
    forall|i: int| 1 <= i < refs.len() ==> origin(#[trigger] refs[i].id) == origin(refs[0].id)
}

/// The heartbeat's tasks, one after the other: a held task whose holder is
/// `pid` has its lease extended from `now`, and its end rearmed.
pub open spec fn task_heartbeat_fold(pid: Chars, refs: Seq<TaskRefV>, s: ServerV, n: ServerV, work: Seq<Sched<InternalV>>, extended: bool, now: Time) -> (ServerV, Seq<Sched<InternalV>>, bool)
    decreases refs.len(),
{
    if refs.len() == 0 {
        (n, work, extended)
    } else {
        let (n1, work1, ext1) = task_heartbeat_fold(pid, refs.drop_last(), s, n, work, extended, now);
        let r = refs.last();
        match held_v(s, r.id, r.version) {
            Ok(t) => {
                let mine = t.pid is Some && t.pid.unwrap() == pid;
                if mine {
                    let u = TaskV { acquired_at: now, ..t };
                    (ServerV { tasks: n1.tasks.insert(r.id, u), ..n1 }, work1.push(at_v(lease_expires_v(u), r.id)), true)
                } else {
                    (n1, work1, ext1)
                }
            },
            Err(_) => (n1, work1, ext1),
        }
    }
}

pub open spec fn task_heartbeat_v(pid: Chars, refs: Seq<TaskRefV>, s: ServerV, now: Time) -> Seq<OutV> {
    if !one_origin(refs) {
        status_v(400, s)
    } else {
        let (n, work, _) = task_heartbeat_fold(pid, refs, s, s, Seq::empty(), false, now);
        one_v(ResponseV::Status(200), n, work, Seq::empty())
    }
}

pub open spec fn distinct(ids: Seq<Chars>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ids.len() ==> ids[i] != ids[j]
}

pub open spec fn all_in_origin(ids: Seq<Chars>, id: Chars) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> origin(#[trigger] ids[i]) == origin(id)
}

pub open spec fn all_present(ids: Seq<Chars>, s: ServerV) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> s.promises.contains_key(#[trigger] ids[i])
}

pub open spec fn all_external(ids: Seq<Chars>, s: ServerV) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> external_v(s.promises[#[trigger] ids[i]])
}

pub open spec fn any_settled(ids: Seq<Chars>, s: ServerV) -> bool {
    exists|i: int| 0 <= i < ids.len() && !live_v(s.promises[#[trigger] ids[i]])
}

/// `id` registered as a callback on each awaited promise.
pub open spec fn with_callbacks(promises: Map<Chars, PromiseV>, ids: Seq<Chars>, id: Chars) -> Map<Chars, PromiseV>
    decreases ids.len(),
{
    if ids.len() == 0 {
        promises
    } else {
        let m = with_callbacks(promises, ids.drop_last(), id);
        let a = ids.last();
        if m.contains_key(a) {
            m.insert(a, PromiseV { callbacks: m[a].callbacks.insert(id), ..m[a] })
        } else {
            m
        }
    }
}

pub open spec fn task_suspend_v(id: Chars, version: u32, ids: Seq<Chars>, s: ServerV) -> Seq<OutV> {
    if ids.len() == 0 || ids.contains(id) {
        status_v(400, s)
    } else if !distinct(ids) {
        status_v(400, s)
    } else if !all_in_origin(ids, id) {
        status_v(400, s)
    } else {
        match held_v(s, id, version) {
            Err(code) => status_v(code, s),
            Ok(t) => {
                if !all_present(ids, s) {
                    status_v(422, s)
                } else if !all_external(ids, s) {
                    status_v(422, s)
                } else if any_settled(ids, s) {
                    // The task stays acquired and runs on; what it was told has been seen.
                    one_v(ResponseV::Status(300), ServerV { tasks: s.tasks.insert(id, TaskV { resumes: Seq::empty(), ..t }), ..s }, Seq::empty(), Seq::empty())
                } else {
                    let u = TaskV { state: TState::Suspended, pid: None, ttl: None, acquired_at: 0, retry_at: None, resumes: Seq::empty(), ..t };
                    one_v(
                        ResponseV::Status(200),
                        ServerV { promises: with_callbacks(s.promises, ids, id), tasks: s.tasks.insert(id, u), ..s },
                        Seq::empty(),
                        Seq::empty(),
                    )
                }
            },
        }
    }
}

pub open spec fn fenced_target(a: FencedV) -> Chars {
    match a {
        FencedV::Create(c) => c.id,
        FencedV::Settle(st) => st.id,
    }
}

/// A fence that creates a promise in another origin: the create first, as a
/// request of its own, then the fence's check decides the answer.
pub open spec fn task_fence_detached_v(id: Chars, version: u32, c: CreateV, s: ServerV, now: Time) -> Seq<OutV> {
    let outs = promise_create_v(c, s, now);
    let o = outs[0];
    match held_v(o.next, id, version) {
        Err(code) => one_v(ResponseV::Status(code), o.next, o.work, o.send),
        Ok(_) => one_v(o.resp, o.next, o.work, o.send),
    }
}

pub open spec fn task_fence_v(id: Chars, version: u32, action: FencedV, s: ServerV, now: Time) -> Seq<OutV> {
    if fenced_target(action) == id {
        status_v(400, s)
    } else if (match action {
        FencedV::Create(c) => c.tags.delay is Some && c.tags.delay.unwrap() >= c.timeout_at,
        FencedV::Settle(_) => false,
    }) {
        status_v(400, s)
    } else if (match action {
        FencedV::Create(c) => c.tags.delay is Some && !c.tags.target,
        FencedV::Settle(_) => false,
    }) {
        status_v(400, s)
    } else {
        match action {
            FencedV::Settle(st) => {
                if origin(st.id) != origin(id) {
                    status_v(400, s)
                } else {
                    match held_v(s, id, version) {
                        Err(code) => status_v(code, s),
                        Ok(_) => promise_settle_v(st, s, now),
                    }
                }
            },
            FencedV::Create(c) => {
                if origin(c.id) != origin(id) {
                    task_fence_detached_v(id, version, c, s, now)
                } else {
                    match held_v(s, id, version) {
                        Err(code) => status_v(code, s),
                        Ok(_) => promise_create_v(c, s, now),
                    }
                }
            },
        }
    }
}

pub open spec fn task_halt_v(id: Chars, s: ServerV) -> Seq<OutV> {
    if !s.tasks.contains_key(id) {
        status_v(404, s)
    } else {
        let t = s.tasks[id];
        match t.state {
            TState::Fulfilled => status_v(409, s),
            TState::Halted => status_v(200, s),
            _ => {
                let u = TaskV { state: TState::Halted, pid: None, ttl: None, acquired_at: 0, retry_at: None, ..t };
                one_v(ResponseV::Status(200), ServerV { tasks: s.tasks.insert(id, u), ..s }, Seq::empty(), Seq::empty())
            },
        }
    }
}

pub open spec fn task_continue_v(id: Chars, s: ServerV, now: Time) -> Seq<OutV> {
    if !s.tasks.contains_key(id) {
        status_v(404, s)
    } else {
        let t = s.tasks[id];
        let live = s.promises.contains_key(id) && live_v(s.promises[id]);
        if t.state != TState::Halted || !live {
            status_v(409, s)
        } else {
            let u = TaskV { state: TState::Pending, retry_at: Some(now), ..t };
            one_v(ResponseV::Status(200), ServerV { tasks: s.tasks.insert(id, u), ..s }, seq![at_v(now, id)], Seq::empty())
        }
    }
}

/// The work that fires `schedule`'s occurrence at `at`: later, from `at` on,
/// and a timer at `at + fire_within`; with `fire_within` zero, the timer alone.
pub open spec fn arm_fire_v(cfg: Resonate, schedule: Chars, at: Time, template: Chars) -> Seq<Sched<InternalV>> {
    let step = InternalV::Fire { schedule, at, promise: spec_expand(template, schedule, at) };
    let timer = Sched::Timer(sat_add(at, cfg.fire_within), step);
    if cfg.fire_within > 0 {
        seq![Sched::Later(step), timer]
    } else {
        seq![timer]
    }
}

pub open spec fn schedule_create_v(cfg: Resonate, req: ScheduleCreateV, s: ServerV, now: Time) -> Seq<OutV> {
    if spec_has_colon(req.id) {
        status_v(400, s)
    } else if !req.promise_tags.target {
        status_v(400, s)
    } else if req.promise_tags.timer && req.promise_tags.target {
        status_v(400, s)
    } else if !spec_cron_valid(req.cron) {
        status_v(400, s)
    } else if s.schedules.contains_key(req.id) {
        echo_v(ResponseV::Schedule(s.schedules[req.id]), s)
    } else {
        let next = spec_next_cron(req.cron, now);
        let c = ScheduleV {
            id: req.id,
            cron: req.cron,
            promise_id: req.promise_id,
            promise_timeout: req.promise_timeout,
            promise_param: req.promise_param,
            promise_tags: req.promise_tags,
            created_at: now,
            next_run_at: next,
            last_run_at: None,
        };
        one_v(ResponseV::Schedule(c), ServerV { schedules: s.schedules.insert(req.id, c), ..s }, arm_fire_v(cfg, req.id, next, req.promise_id), Seq::empty())
    }
}

pub open spec fn schedule_delete_v(id: Chars, s: ServerV) -> Seq<OutV> {
    if !s.schedules.contains_key(id) {
        status_v(404, s)
    } else {
        one_v(ResponseV::Status(200), ServerV { schedules: s.schedules.remove(id), ..s }, Seq::empty(), Seq::empty())
    }
}

/// A request takes effect in `s` at time `now`: every allowed outcome.
pub open spec fn ext(cfg: Resonate, op: RequestV, s: ServerV, now: Time) -> Seq<OutV> {
    match op {
        RequestV::CreatePromise(c) => promise_create_v(c, s, now),
        RequestV::GetPromise(id) => if s.promises.contains_key(id) {
            echo_v(ResponseV::Promise(prec_v(id, s.promises[id])), s)
        } else {
            status_v(404, s)
        },
        RequestV::SettlePromise(st) => promise_settle_v(st, s, now),
        RequestV::RegisterCallback { awaited, awaiter } => promise_register_callback_v(awaited, awaiter, s),
        RequestV::RegisterListener { awaited, address } => promise_register_listener_v(awaited, address, s),
        RequestV::GetTask(id) => if s.tasks.contains_key(id) {
            echo_v(ResponseV::Task(trec_v(id, s.tasks[id])), s)
        } else {
            status_v(404, s)
        },
        RequestV::CreateTask { pid, ttl, action } => task_create_v(pid, ttl, action, s, now),
        RequestV::AcquireTask { id, version, pid, ttl } => task_acquire_v(id, version, pid, ttl, s, now),
        RequestV::ReleaseTask { id, version } => task_release_v(id, version, s, now),
        RequestV::FulfillTask { id, version, state, data } => task_fulfill_v(id, version, state, data, s, now),
        RequestV::HeartbeatTask { pid, tasks } => task_heartbeat_v(pid, tasks, s, now),
        RequestV::SuspendTask { id, version, awaited } => task_suspend_v(id, version, awaited, s),
        RequestV::FenceTask { id, version, action } => task_fence_v(id, version, action, s, now),
        RequestV::HaltTask(id) => task_halt_v(id, s),
        RequestV::ContinueTask(id) => task_continue_v(id, s, now),
        RequestV::CreateSchedule(c) => schedule_create_v(cfg, c, s, now),
        RequestV::GetSchedule(id) => if s.schedules.contains_key(id) {
            echo_v(ResponseV::Schedule(s.schedules[id]), s)
        } else {
            status_v(404, s)
        },
        RequestV::DeleteSchedule(id) => schedule_delete_v(id, s),
    }
}

// ------------------------------------------------------------ internal work

/// A suspended task resumes when a promise it awaits has settled; any other
/// task is told, when it next runs. The callback is spent either way.
pub open spec fn resume_v(n: ServerV, awaited: Chars, awaiter: Chars, now: Time) -> ServerV {
    let since = if n.promises.contains_key(awaited) && n.promises[awaited].settled_at is Some { n.promises[awaited].settled_at.unwrap() } else { now };
    let promises = if n.promises.contains_key(awaited) {
        let p = n.promises[awaited];
        n.promises.insert(awaited, PromiseV { callbacks: p.callbacks.remove(awaiter), ..p })
    } else {
        n.promises
    };
    let tasks = if n.tasks.contains_key(awaiter) {
        let t = n.tasks[awaiter];
        match t.state {
            TState::Suspended => n.tasks.insert(awaiter, TaskV { state: TState::Pending, resumes: seq![awaited], retry_at: Some(since), ..t }),
            TState::Fulfilled => n.tasks,
            _ => if !t.resumes.contains(awaited) { n.tasks.insert(awaiter, TaskV { resumes: t.resumes.push(awaited), ..t }) } else { n.tasks },
        }
    } else {
        n.tasks
    };
    ServerV { promises, tasks, ..n }
}

/// Phase 1: a promise past its deadline times out (a timer promise resolves),
/// and starts its resumes and unblocks.
pub open spec fn deadlines_fold(ids: Seq<Chars>, n: ServerV, work: Seq<Sched<InternalV>>, now: Time) -> (ServerV, Seq<Sched<InternalV>>)
    decreases ids.len(),
{
    if ids.len() == 0 {
        (n, work)
    } else {
        let (n1, work1) = deadlines_fold(ids.drop_last(), n, work, now);
        let id = ids.last();
        if n1.promises.contains_key(id) && live_v(n1.promises[id]) && now >= n1.promises[id].timeout_at {
            let p = n1.promises[id];
            let state = if p.tags.timer { PState::Resolved } else { PState::TimedOut };
            (settle_v(n1, id, state, None, p.timeout_at), work1 + settled_work_v(p, id))
        } else {
            (n1, work1)
        }
    }
}

/// Phase 2: every callback among `ids` on a settled promise among `ids` is
/// spent: its awaiter resumes.
pub open spec fn resumes_inner(awaited: Chars, awaiters: Seq<Chars>, n: ServerV, now: Time) -> ServerV
    decreases awaiters.len(),
{
    if awaiters.len() == 0 {
        n
    } else {
        let n1 = resumes_inner(awaited, awaiters.drop_last(), n, now);
        let awaiter = awaiters.last();
        let due = n1.promises.contains_key(awaited) && !live_v(n1.promises[awaited]) && n1.promises[awaited].callbacks.contains(awaiter);
        if due { resume_v(n1, awaited, awaiter, now) } else { n1 }
    }
}

pub open spec fn resumes_fold(awaiteds: Seq<Chars>, all: Seq<Chars>, n: ServerV, now: Time) -> ServerV
    decreases awaiteds.len(),
{
    if awaiteds.len() == 0 {
        n
    } else {
        let n1 = resumes_fold(awaiteds.drop_last(), all, n, now);
        resumes_inner(awaiteds.last(), all, n1, now)
    }
}

/// Phase 3, per object: a task past its lease is reclaimed, offered again from
/// the lease's end; a settled promise's listeners are told, once; a pending
/// task whose retry is due is offered to a worker and the next offer armed.
pub open spec fn due_fold(cfg: Resonate, ids: Seq<Chars>, n: ServerV, work: Seq<Sched<InternalV>>, send: Seq<DispatchV>, now: Time) -> (ServerV, Seq<Sched<InternalV>>, Seq<DispatchV>)
    decreases ids.len(),
{
    if ids.len() == 0 {
        (n, work, send)
    } else {
        let (n1, work1, send1) = due_fold(cfg, ids.drop_last(), n, work, send, now);
        let id = ids.last();
        // the lease
        let tasks2 = if n1.tasks.contains_key(id) && n1.tasks[id].state == TState::Acquired && now >= lease_expires_v(n1.tasks[id]) {
            n1.tasks.insert(id, released_v(n1.tasks[id], lease_expires_v(n1.tasks[id])))
        } else {
            n1.tasks
        };
        let n2 = ServerV { tasks: tasks2, ..n1 };
        // the listeners
        let told = n2.promises.contains_key(id) && !live_v(n2.promises[id]) && n2.promises[id].listeners.len() > 0;
        let (n3, send3) = if told {
            let p = n2.promises[id];
            let rec = prec_v(id, p);
            let unblocks = pset_seq(p.listeners).map_values(|a: Chars| DispatchV::Unblock { address: a, promise: rec });
            (ServerV { promises: n2.promises.insert(id, PromiseV { listeners: Set::empty(), ..p }), ..n2 }, send1 + unblocks)
        } else {
            (n2, send1)
        };
        // the retry
        let live = n3.promises.contains_key(id) && live_v(n3.promises[id]);
        let retry = n3.tasks.contains_key(id) && {
            let t = n3.tasks[id];
            t.state == TState::Pending && t.retry_at is Some && t.retry_at.unwrap() <= now && live
        };
        if retry {
            let t = n3.tasks[id];
            let again = next_offer_v(t.retry_at.unwrap(), now, cfg.retry_timeout);
            (
                ServerV { tasks: n3.tasks.insert(id, TaskV { retry_at: Some(again), ..t }), ..n3 },
                work1.push(at_v(again, id)),
                send3.push(DispatchV::Execute { id, version: t.version }),
            )
        } else {
            (n3, work1, send3)
        }
    }
}

/// Internal work on `ids` runs in `s` at time `now`: whatever is due on them
/// happens, in the order the Lean specification's steps become enabled.
pub open spec fn on_v(cfg: Resonate, ids: Seq<Chars>, s: ServerV, now: Time) -> InOutV {
    let (n1, work1) = deadlines_fold(ids, s, Seq::empty(), now);
    let n2 = resumes_fold(ids, ids, n1, now);
    let (n3, work3, send3) = due_fold(cfg, ids, n2, work1, Seq::empty(), now);
    InOutV { next: n3, work: work3, send: send3, pending: false }
}

pub open spec fn noop_v(s: ServerV, pending: bool) -> InOutV {
    InOutV { next: s, work: Seq::empty(), send: Seq::empty(), pending }
}

pub open spec fn record_run_v(c: ScheduleV, at: Time) -> ScheduleV {
    ScheduleV { last_run_at: Some(at), next_run_at: spec_next_cron(c.cron, at), ..c }
}

/// A schedule's occurrence at `at` fires: the promise it names is created, if
/// absent, as of `at` (born settled when its deadline has passed by `now`);
/// the run is recorded at once, or by `advance_v` within the window.
pub open spec fn fire_v(cfg: Resonate, schedule: Chars, at: Time, promise: Chars, s: ServerV, now: Time) -> InOutV {
    if !s.schedules.contains_key(schedule) {
        noop_v(s, false)
    } else {
        let c = s.schedules[schedule];
        if c.next_run_at != at || spec_expand(c.promise_id, schedule, at) != promise {
            noop_v(s, false)
        } else if now < at {
            noop_v(s, true)
        } else {
            let (n1, work1) = if s.promises.contains_key(promise) {
                (s, Seq::<Sched<InternalV>>::empty())
            } else {
                let timeout_at = sat_add(at, c.promise_timeout);
                let tags = c.promise_tags;
                let live_now = timeout_at > now;
                let live_at = timeout_at > at;
                let born = if live_now { PState::Pending } else if tags.timer { PState::Resolved } else { PState::TimedOut };
                let p = PromiseV {
                    state: born,
                    value: None,
                    param: c.promise_param,
                    timeout_at,
                    created_at: if live_at { at } else { timeout_at },
                    settled_at: if live_now { None } else { Some(timeout_at) },
                    tags,
                    callbacks: Set::empty(),
                    listeners: Set::empty(),
                };
                let promises = s.promises.insert(promise, p);
                let work0: Seq<Sched<InternalV>> = if live_now { seq![at_v(timeout_at, promise)] } else { Seq::empty() };
                if tags.target && !tags.timer {
                    let due = match tags.delay {
                        Some(d) => if d > at { d } else { at },
                        None => at,
                    };
                    let task = TaskV {
                        state: if live_now { TState::Pending } else { TState::Fulfilled },
                        version: 0,
                        pid: None,
                        ttl: None,
                        acquired_at: 0,
                        retry_at: if live_now { Some(due) } else { None },
                        resumes: Seq::empty(),
                    };
                    (ServerV { promises, tasks: s.tasks.insert(promise, task), ..s }, if live_now { work0.push(at_v(due, promise)) } else { work0 })
                } else {
                    (ServerV { promises, ..s }, work0)
                }
            };
            if cfg.fire_within == 0 {
                let d = record_run_v(c, at);
                InOutV {
                    next: ServerV { schedules: n1.schedules.insert(schedule, d), ..n1 },
                    work: work1 + arm_fire_v(cfg, schedule, d.next_run_at, c.promise_id),
                    send: Seq::empty(),
                    pending: false,
                }
            } else {
                let step = InternalV::Advance { schedule, at, promise };
                InOutV {
                    next: n1,
                    work: work1 + seq![Sched::Later(step), Sched::Timer(sat_add(at, cfg.fire_within), step)],
                    send: Seq::empty(),
                    pending: false,
                }
            }
        }
    }
}

/// The second half of a sweeping server's fire: the run at `at` recorded and
/// the next occurrence armed.
pub open spec fn advance_v(cfg: Resonate, schedule: Chars, at: Time, promise: Chars, s: ServerV, now: Time) -> InOutV {
    if !s.schedules.contains_key(schedule) {
        noop_v(s, false)
    } else {
        let c = s.schedules[schedule];
        if c.next_run_at != at || spec_expand(c.promise_id, schedule, at) != promise {
            noop_v(s, false)
        } else if now < at {
            noop_v(s, true)
        } else {
            let d = record_run_v(c, at);
            InOutV {
                next: ServerV { schedules: s.schedules.insert(schedule, d), ..s },
                work: arm_fire_v(cfg, schedule, d.next_run_at, c.promise_id),
                send: Seq::empty(),
                pending: false,
            }
        }
    }
}

pub open spec fn int(cfg: Resonate, step: InternalV, s: ServerV, now: Time) -> InOutV {
    match step {
        InternalV::On(ids) => on_v(cfg, ids, s, now),
        InternalV::Fire { schedule, at, promise } => fire_v(cfg, schedule, at, promise, s, now),
        InternalV::Advance { schedule, at, promise } => advance_v(cfg, schedule, at, promise, s, now),
    }
}

// ----------------------------------------------- the twins, over the values

/// The value of the model's type with this view. That one exists is
/// `axiom_realised`: the types are built to hold any finite view.
pub open spec fn lift_server(v: ServerV) -> Server {
    choose|x: Server| x@ == v
}

pub open spec fn lift_response(v: ResponseV) -> Response {
    choose|x: Response| x@ == v
}

pub open spec fn lift_internal(v: InternalV) -> Internal {
    choose|x: Internal| x@ == v
}

pub open spec fn lift_dispatch(v: DispatchV) -> Dispatch {
    choose|x: Dispatch| x@ == v
}

pub open spec fn lift_sched(s: Sched<InternalV>) -> Sched<Internal> {
    match s {
        Sched::Later(r) => Sched::Later(lift_internal(r)),
        Sched::Timer(t, r) => Sched::Timer(t, lift_internal(r)),
    }
}

pub open spec fn lift_out(o: OutV) -> ExternalOutcomeV<Server, Response, Internal, Dispatch> {
    ExternalOutcomeV {
        next: lift_server(o.next),
        resp: lift_response(o.resp),
        work: o.work.map_values(|w: Sched<InternalV>| lift_sched(w)),
        send: o.send.map_values(|d: DispatchV| lift_dispatch(d)),
    }
}

pub open spec fn lift_inout(o: InOutV) -> InternalOutcomeV<Server, Internal, Dispatch> {
    InternalOutcomeV {
        next: lift_server(o.next),
        work: o.work.map_values(|w: Sched<InternalV>| lift_sched(w)),
        send: o.send.map_values(|d: DispatchV| lift_dispatch(d)),
    }
}

/// Every view the twins produce is some value's view. Trusted: the maps and
/// sets hold any finite contents, strings any characters. Stated for the
/// views the twins reach (finite, since they come from values).
#[verifier::external_body]
pub proof fn axiom_realised(v: ServerV, r: ResponseV, i: InternalV, d: DispatchV)
    ensures
        lift_server(v)@ == v,
        lift_response(r)@ == r,
        lift_internal(i)@ == i,
        lift_dispatch(d)@ == d,
{
}

// --------------------------------------------------- a value is its view

pub proof fn lemma_ostr_ext(a: Option<String>, b: Option<String>)
    requires
        ostr(a) == ostr(b),
    ensures
        a == b,
{
    match (a, b) {
        (Some(x), Some(y)) => axiom_string_ext(x, y),
        _ => {},
    }
}

pub proof fn lemma_strs_ext(a: Vec<String>, b: Vec<String>)
    requires
        strs(a@) == strs(b@),
    ensures
        a == b,
{
    broadcast use group_views;
    assert(strs(a@).len() == a@.len());
    assert(strs(b@).len() == b@.len());
    assert forall|i: int| 0 <= i < a@.len() implies a@[i] == b@[i] by {
        assert(strs(a@)[i] == a@[i]@);
        assert(strs(b@)[i] == b@[i]@);
        axiom_string_ext(a@[i], b@[i]);
    }
    assert(a@ =~= b@);
    axiom_vec_ext(a, b);
}

pub proof fn lemma_promise_ext(a: Promise, b: Promise)
    requires
        a@ == b@,
    ensures
        a == b,
{
    lemma_ostr_ext(a.value, b.value);
    lemma_ostr_ext(a.param, b.param);
    axiom_pset_ext(a.callbacks, b.callbacks);
    axiom_pset_ext(a.listeners, b.listeners);
}

pub proof fn lemma_task_ext(a: Task, b: Task)
    requires
        a@ == b@,
    ensures
        a == b,
{
    lemma_ostr_ext(a.pid, b.pid);
    lemma_strs_ext(a.resumes, b.resumes);
}

pub proof fn lemma_schedule_ext(a: Schedule, b: Schedule)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
    axiom_string_ext(a.cron, b.cron);
    axiom_string_ext(a.promise_id, b.promise_id);
    lemma_ostr_ext(a.promise_param, b.promise_param);
}

pub proof fn lemma_promises_ext(a: PMap<Promise>, b: PMap<Promise>)
    requires
        a@.map_values(|p: Promise| p@) == b@.map_values(|p: Promise| p@),
    ensures
        a == b,
{
    let f = |p: Promise| p@;
    assert forall|k: Chars| a@.contains_key(k) implies b@.contains_key(k) && a@[k] == b@[k] by {
        assert(a@.map_values(f).contains_key(k));
        assert(b@.map_values(f).contains_key(k));
        assert(a@.map_values(f)[k] == b@.map_values(f)[k]);
        lemma_promise_ext(a@[k], b@[k]);
    }
    assert forall|k: Chars| b@.contains_key(k) implies a@.contains_key(k) by {
        assert(b@.map_values(f).contains_key(k));
    }
    assert(a@ =~= b@);
    axiom_pmap_ext(a, b);
}

pub proof fn lemma_tasks_ext(a: PMap<Task>, b: PMap<Task>)
    requires
        a@.map_values(|t: Task| t@) == b@.map_values(|t: Task| t@),
    ensures
        a == b,
{
    let f = |t: Task| t@;
    assert forall|k: Chars| a@.contains_key(k) implies b@.contains_key(k) && a@[k] == b@[k] by {
        assert(a@.map_values(f).contains_key(k));
        assert(b@.map_values(f).contains_key(k));
        assert(a@.map_values(f)[k] == b@.map_values(f)[k]);
        lemma_task_ext(a@[k], b@[k]);
    }
    assert forall|k: Chars| b@.contains_key(k) implies a@.contains_key(k) by {
        assert(b@.map_values(f).contains_key(k));
    }
    assert(a@ =~= b@);
    axiom_pmap_ext(a, b);
}

pub proof fn lemma_schedules_ext(a: PMap<Schedule>, b: PMap<Schedule>)
    requires
        a@.map_values(|c: Schedule| c@) == b@.map_values(|c: Schedule| c@),
    ensures
        a == b,
{
    let f = |c: Schedule| c@;
    assert forall|k: Chars| a@.contains_key(k) implies b@.contains_key(k) && a@[k] == b@[k] by {
        assert(a@.map_values(f).contains_key(k));
        assert(b@.map_values(f).contains_key(k));
        assert(a@.map_values(f)[k] == b@.map_values(f)[k]);
        lemma_schedule_ext(a@[k], b@[k]);
    }
    assert forall|k: Chars| b@.contains_key(k) implies a@.contains_key(k) by {
        assert(b@.map_values(f).contains_key(k));
    }
    assert(a@ =~= b@);
    axiom_pmap_ext(a, b);
}

pub proof fn lemma_server_ext(a: Server, b: Server)
    requires
        a@ == b@,
    ensures
        a == b,
{
    lemma_promises_ext(a.promises, b.promises);
    lemma_tasks_ext(a.tasks, b.tasks);
    lemma_schedules_ext(a.schedules, b.schedules);
}

pub proof fn lemma_prec_ext(a: PromiseRec, b: PromiseRec)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
    lemma_ostr_ext(a.param, b.param);
    lemma_ostr_ext(a.value, b.value);
}

pub proof fn lemma_trec_ext(a: TaskRec, b: TaskRec)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
    lemma_ostr_ext(a.pid, b.pid);
}

pub proof fn lemma_response_ext(a: Response, b: Response)
    requires
        a@ == b@,
    ensures
        a == b,
{
    match (a, b) {
        (Response::Status(_), Response::Status(_)) => {},
        (Response::Promise(p), Response::Promise(q)) => lemma_prec_ext(p, q),
        (Response::Task(t), Response::Task(u)) => lemma_trec_ext(t, u),
        (Response::Both(p, t), Response::Both(q, u)) => {
            lemma_prec_ext(p, q);
            lemma_trec_ext(t, u);
        },
        (Response::Schedule(c), Response::Schedule(d)) => lemma_schedule_ext(c, d),
        _ => {},
    }
}

pub proof fn lemma_internal_ext(a: Internal, b: Internal)
    requires
        a@ == b@,
    ensures
        a == b,
{
    match (a, b) {
        (Internal::On(x), Internal::On(y)) => lemma_strs_ext(x, y),
        (Internal::Fire { schedule: s1, promise: p1, .. }, Internal::Fire { schedule: s2, promise: p2, .. }) => {
            axiom_string_ext(s1, s2);
            axiom_string_ext(p1, p2);
        },
        (Internal::Advance { schedule: s1, promise: p1, .. }, Internal::Advance { schedule: s2, promise: p2, .. }) => {
            axiom_string_ext(s1, s2);
            axiom_string_ext(p1, p2);
        },
        _ => {},
    }
}

pub proof fn lemma_dispatch_ext(a: Dispatch, b: Dispatch)
    requires
        a@ == b@,
    ensures
        a == b,
{
    match (a, b) {
        (Dispatch::Execute { id: x, .. }, Dispatch::Execute { id: y, .. }) => axiom_string_ext(x, y),
        (Dispatch::Unblock { address: x, promise: p }, Dispatch::Unblock { address: y, promise: q }) => {
            axiom_string_ext(x, y);
            lemma_prec_ext(p, q);
        },
        _ => {},
    }
}

// ----------------------------------------------- the lift of a value's view

pub proof fn lemma_lift_server(s: Server)
    ensures
        lift_server(s@) == s,
{
    axiom_realised(s@, ResponseV::Status(0), InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    lemma_server_ext(lift_server(s@), s);
}

pub proof fn lemma_lift_response(r: Response)
    ensures
        lift_response(r@) == r,
{
    axiom_realised(ServerV { promises: Map::empty(), tasks: Map::empty(), schedules: Map::empty() }, r@, InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    lemma_response_ext(lift_response(r@), r);
}

pub proof fn lemma_lift_internal(i: Internal)
    ensures
        lift_internal(i@) == i,
{
    axiom_realised(ServerV { promises: Map::empty(), tasks: Map::empty(), schedules: Map::empty() }, ResponseV::Status(0), i@, DispatchV::Execute { id: Seq::empty(), version: 0 });
    lemma_internal_ext(lift_internal(i@), i);
}

pub proof fn lemma_lift_dispatch(d: Dispatch)
    ensures
        lift_dispatch(d@) == d,
{
    axiom_realised(ServerV { promises: Map::empty(), tasks: Map::empty(), schedules: Map::empty() }, ResponseV::Status(0), InternalV::On(Seq::empty()), d@);
    lemma_dispatch_ext(lift_dispatch(d@), d);
}

pub proof fn lemma_lift_sched(w: Sched<Internal>)
    ensures
        lift_sched(sched_v(w)) == w,
{
    match w {
        Sched::Later(r) => lemma_lift_internal(r),
        Sched::Timer(_, r) => lemma_lift_internal(r),
    }
}

/// The checker's outcome built from an `Out` is the lift of the `Out`'s view.
pub proof fn lemma_lift_out(o: ExternalOutcomeV<Server, Response, Internal, Dispatch>, v: OutV)
    requires
        o.next@ == v.next,
        o.resp@ == v.resp,
        o.work.map_values(|w: Sched<Internal>| sched_v(w)) == v.work,
        o.send.map_values(|d: Dispatch| d@) == v.send,
    ensures
        lift_out(v) == o,
{
    lemma_lift_server(o.next);
    lemma_lift_response(o.resp);
    assert forall|j: int| 0 <= j < o.work.len() implies #[trigger] lift_sched(v.work[j]) == o.work[j] by {
        lemma_lift_sched(o.work[j]);
    }
    assert(v.work.map_values(|w: Sched<InternalV>| lift_sched(w)) =~= o.work);
    assert forall|j: int| 0 <= j < o.send.len() implies #[trigger] lift_dispatch(v.send[j]) == o.send[j] by {
        lemma_lift_dispatch(o.send[j]);
    }
    assert(v.send.map_values(|d: DispatchV| lift_dispatch(d)) =~= o.send);
}

pub proof fn lemma_lift_inout(o: InternalOutcomeV<Server, Internal, Dispatch>, v: InOutV)
    requires
        o.next@ == v.next,
        o.work.map_values(|w: Sched<Internal>| sched_v(w)) == v.work,
        o.send.map_values(|d: Dispatch| d@) == v.send,
    ensures
        lift_inout(v) == o,
{
    lemma_lift_server(o.next);
    assert forall|j: int| 0 <= j < o.work.len() implies #[trigger] lift_sched(v.work[j]) == o.work[j] by {
        lemma_lift_sched(o.work[j]);
    }
    assert(v.work.map_values(|w: Sched<InternalV>| lift_sched(w)) =~= o.work);
    assert forall|j: int| 0 <= j < o.send.len() implies #[trigger] lift_dispatch(v.send[j]) == o.send[j] by {
        lemma_lift_dispatch(o.send[j]);
    }
    assert(v.send.map_values(|d: DispatchV| lift_dispatch(d)) =~= o.send);
}

// ------------------------------------------------------------- the model

fn step(s: Step) -> (r: Internal)
    ensures
        r@ == s@,
{
    match s {
        Step::Objects(ids) => Internal::On(ids),
        Step::Fire { schedule, at, promise } => Internal::Fire { schedule, at, promise },
        Step::Advance { schedule, at, promise } => Internal::Advance { schedule, at, promise },
    }
}

fn sched(w: Work) -> (r: Sched<Internal>)
    ensures
        sched_v(r) == w@,
{
    match w {
        Work::Later(s) => Sched::Later(step(s)),
        Work::Timer(at, s) => Sched::Timer(at, step(s)),
    }
}

/// The work an outcome starts, as the checker's items.
fn items(mut w: Vec<Work>) -> (r: Vec<Sched<Internal>>)
    ensures
        r@.map_values(|x: Sched<Internal>| sched_v(x)) == works(w@),
{
    let ghost all = w@;
    let mut r: Vec<Sched<Internal>> = Vec::new();
    while w.len() > 0
        invariant
            r@.len() + w@.len() == all.len(),
            w@ == all.skip(r@.len() as int),
            r@.map_values(|x: Sched<Internal>| sched_v(x)) == works(all.take(r@.len() as int)),
        decreases w@.len(),
    {
        broadcast use group_views;
        let ghost k = r@.len() as int;
        let x = w.remove(0);
        assert(all.skip(k).remove(0) =~= all.skip(k + 1));
        assert(all.take(k + 1) =~= all.take(k).push(all[k]));
        r.push(sched(x));
    }
    assert(all.take(all.len() as int) =~= all);
    r
}

impl Model for Resonate {
    type State = Server;

    type External = Request;

    type Response = Response;

    type Internal = Internal;

    type Dispatch = Dispatch;

    open spec fn spec_external(&self, req: Request, state: Server, now: Time) -> Seq<ExternalOutcomeV<Server, Response, Internal, Dispatch>> {
        ext(*self, req@, state@, now).map_values(|o: OutV| lift_out(o))
    }

    open spec fn spec_internal(&self, req: Internal, state: Server, now: Time) -> Seq<InternalOutcomeV<Server, Internal, Dispatch>> {
        let o = int(*self, req@, state@, now);
        if o.pending { Seq::empty() } else { seq![lift_inout(o)] }
    }

    fn external(&self, op: &Request, s: &Server, now: Time) -> (r: Vec<ExternalOutcome<Self>>) {
        let mut outs = self.request(op, s, now);
        let ghost all = outs@;
        let ghost twin = ext(*self, op@, s@, now);
        assert(twin == outs_v(all));
        let mut r: Vec<ExternalOutcome<Resonate>> = Vec::new();
        while outs.len() > 0
            invariant
                twin == outs_v(all),
                r@.len() + outs@.len() == all.len(),
                outs@ == all.skip(r@.len() as int),
                forall|j: int| 0 <= j < r@.len() ==> {
                    let o = #[trigger] r@[j];
                    ExternalOutcomeV { next: o.next, resp: o.resp, work: o.work@, send: o.send@ } == lift_out(all[j]@)
                },
            decreases outs@.len(),
        {
            let ghost k = r@.len() as int;
            let o = outs.remove(0);
            assert(all.skip(k).remove(0) =~= all.skip(k + 1));
            assert(o == all[k]);
            let Out { resp, next, work, send, marks } = o;
            let work = items(work);
            let e = ExternalOutcome { next, resp, work, send, marks };
            proof {
                lemma_lift_out(ExternalOutcomeV { next: e.next, resp: e.resp, work: e.work@, send: e.send@ }, all[k]@);
            }
            r.push(e);
        }
        proof {
            assert(r@.len() == all.len());
            assert forall|i: int| 0 <= i < r@.len() implies {
                let o = #[trigger] r@[i];
                ExternalOutcomeV { next: o.next, resp: o.resp, work: o.work@, send: o.send@ } == self.spec_external(*op, *s, now)[i]
            } by {
                assert(self.spec_external(*op, *s, now)[i] == lift_out(twin[i]));
                assert(twin[i] == all[i]@);
            }
        }
        r
    }

    fn internal(&self, step: &Internal, s: &Server, now: Time) -> (r: Vec<InternalOutcome<Self>>) {
        let o = match step {
            Internal::On(ids) => self.objects(ids, s, now),
            Internal::Fire { schedule, at, promise } => self.fire(schedule, *at, promise, s, now),
            Internal::Advance { schedule, at, promise } => self.advance(schedule, *at, promise, s, now),
        };
        assert(o@ == int(*self, step@, s@, now));
        let mut r: Vec<InternalOutcome<Resonate>> = Vec::new();
        if o.pending {
            return r;
        }
        let ghost v = o@;
        let InOut { next, work, send, marks, pending: _ } = o;
        let work = items(work);
        let e = InternalOutcome { next, work, send, marks };
        proof {
            lemma_lift_inout(InternalOutcomeV { next: e.next, work: e.work@, send: e.send@ }, v);
        }
        r.push(e);
        r
    }
}

} // verus!
