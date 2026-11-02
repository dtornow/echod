//! Views of the model state, and the lemmas that a value is its view.
//!
//! A request, a response, and a record are the shared types in `echod_types`.
//! Their views live in `echod_types::spec`. The handlers in `exec.rs` are the
//! protocol.
//!
//! Ids and strings view as `Seq<char>`, the persistent maps as `Map`, the
//! sets as `Set`. A value of the model's own types with a given view is
//! obtained by `choose`; that every view is realised by some value is the one
//! axiom this module adds (`axiom_realised`), true of the types as built; that
//! a value is its view (`collections.rs`) makes the choice the value itself.

// Outside Verus (`cargo build`) the spec functions and proofs are erased, and
// the imports they use with them.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::prelude::*;

use echod_rover::semantics::{ExternalOutcomeV, InternalOutcomeV};
use echod_rover::{ExternalOutcome, InternalOutcome, Model, Sched};

use echod_types::{PromiseRecord, PromiseState, Request, Response, Tags, TaskRecord, TaskState, Value};

use super::collections::*;
use super::exec::*;

verus! {

// ------------------------------------------------------------------- views

pub type Chars = Seq<char>;

pub struct PromiseV {
    pub state: PromiseState,
    pub value: Value,
    pub param: Value,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub tags: Tags,
    pub callbacks: Set<Chars>,
    pub listeners: Set<Chars>,
}

pub struct TaskV {
    pub state: TaskState,
    pub version: u64,
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
    pub promise_param: Value,
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

pub enum DispatchV {
    Execute { id: Chars, version: u64 },
    Unblock { address: Chars, promise: PromiseRecord },
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
            value: self.value,
            param: self.param,
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
    pub resp: Response,
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

pub open spec fn distinct(ids: Seq<Chars>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ids.len() ==> ids[i] != ids[j]
}

pub open spec fn all_in_origin(ids: Seq<Chars>, id: Chars) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> origin(#[trigger] ids[i]) == origin(id)
}

// ----------------------------------------------- a value for a view

/// The value of the model's type with this view. That one exists is
/// `axiom_realised`: the types are built to hold any finite view.
pub open spec fn lift_server(v: ServerV) -> Server {
    choose|x: Server| x@ == v
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
        resp: o.resp,
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

/// Every view the handlers produce is some value's view. Trusted: the maps and
/// sets hold any finite contents, strings any characters. Stated for the
/// views the handlers reach (finite, since they come from values).
#[verifier::external_body]
pub proof fn axiom_realised(v: ServerV, i: InternalV, d: DispatchV)
    ensures
        lift_server(v)@ == v,
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

pub proof fn lemma_prec_ext(a: PromiseRecord, b: PromiseRecord)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
}

pub proof fn lemma_trec_ext(a: TaskRecord, b: TaskRecord)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
    match (a.pid, b.pid) {
        (Some(x), Some(y)) => axiom_string_ext(x, y),
        _ => {},
    }
}

pub proof fn lemma_response_ext(a: Response, b: Response)
    requires
        a@ == b@,
    ensures
        a == b,
{
    match (a, b) {
        (Response::Status(_), Response::Status(_)) => {},
        (Response::Promise(p), Response::Promise(q)) => match (p.promise, q.promise) {
            (Some(x), Some(y)) => lemma_prec_ext(x, y),
            _ => {},
        },
        (Response::TaskGet(t), Response::TaskGet(u)) => match (t.task, u.task) {
            (Some(x), Some(y)) => lemma_trec_ext(x, y),
            _ => {},
        },
        (Response::TaskClaim(t), Response::TaskClaim(u)) => {
            match (t.promise, u.promise) {
                (Some(x), Some(y)) => lemma_prec_ext(x, y),
                _ => {},
            }
            match (t.task, u.task) {
                (Some(x), Some(y)) => lemma_trec_ext(x, y),
                _ => {},
            }
        },
        (Response::TaskFence(_), Response::TaskFence(_)) => {},
        (Response::Schedule(c), Response::Schedule(d)) => match (c.schedule, d.schedule) {
            (Some(x), Some(y)) => lemma_schedule_ext(x, y),
            _ => {},
        },
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
    axiom_realised(s@, InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    lemma_server_ext(lift_server(s@), s);
}

pub proof fn lemma_lift_internal(i: Internal)
    ensures
        lift_internal(i@) == i,
{
    axiom_realised(ServerV { promises: Map::empty(), tasks: Map::empty(), schedules: Map::empty() }, i@, DispatchV::Execute { id: Seq::empty(), version: 0 });
    lemma_internal_ext(lift_internal(i@), i);
}

pub proof fn lemma_lift_dispatch(d: Dispatch)
    ensures
        lift_dispatch(d@) == d,
{
    axiom_realised(ServerV { promises: Map::empty(), tasks: Map::empty(), schedules: Map::empty() }, InternalV::On(Seq::empty()), d@);
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
        o.resp == v.resp,
        o.work.map_values(|w: Sched<Internal>| sched_v(w)) == v.work,
        o.send.map_values(|d: Dispatch| d@) == v.send,
    ensures
        lift_out(v) == o,
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

    fn external(&self, op: &Request, s: &Server, now: Time) -> (r: Vec<ExternalOutcome<Self>>) {
        let mut outs = self.request(op, s, now);
        let mut r: Vec<ExternalOutcome<Resonate>> = Vec::new();
        while outs.len() > 0
            decreases outs@.len(),
        {
            let o = outs.remove(0);
            let Out { resp, next, work, send, marks } = o;
            let work = items(work);
            let e = ExternalOutcome { next, resp, work, send, marks };
            r.push(e);
        }
        r
    }

    fn internal(&self, step: &Internal, s: &Server, now: Time) -> (r: Vec<InternalOutcome<Self>>) {
        let o = match step {
            Internal::On(ids) => self.objects(ids, s, now),
            Internal::Fire { schedule, at, promise } => self.fire(schedule, *at, promise, s, now),
            Internal::Advance { schedule, at, promise } => self.advance(schedule, *at, promise, s, now),
        };
        let mut r: Vec<InternalOutcome<Resonate>> = Vec::new();
        if o.pending {
            return r;
        }
        let InOut { next, work, send, marks, pending: _ } = o;
        let work = items(work);
        let e = InternalOutcome { next, work, send, marks };
        r.push(e);
        r
    }
}

} // verus!
