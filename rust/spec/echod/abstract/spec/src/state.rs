//! Mathematical state, its views, and primitive state operations.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use rover_spec::rover::comm::Sched;
use echod_types::{
    PromiseRecord, PromiseRes, PromiseState, Request, Response, Schedule, ScheduleRes, StatusRes,
    Tags, TaskClaimRes, TaskFenceInnerRes, TaskFenceRes, TaskGetRes, TaskRecord, TaskState, Value,
};
use super::protocol::Dispatch;
use super::axioms::*;

pub type Time = u64;

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
    pub retry_timeout_at: Option<Time>,
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

pub struct StoreV {
    pub promises: Map<Chars, PromiseV>,
    pub tasks: Map<Chars, TaskV>,
    pub schedules: Map<Chars, ScheduleV>,
}

pub enum DispatchV {
    Execute { id: Chars, version: u64 },
    Unblock { address: Chars, promise: PromiseRecord },
}

pub enum InternalV {
    PromiseTimeout(Chars),
    Callback { awaited: Chars, awaiter: Chars },
    Listener { awaited: Chars, address: Chars },
    TaskLeaseTimeout(Chars),
    TaskRetryTimeout(Chars),
    ScheduleTimeout { id: Chars, promise: Chars },
    Occurrence { promise: Chars, at: Time, timeout: Time, param: Value, tags: Tags },
}

pub struct OutV {
    pub resp: Response,
    pub next: StoreV,
    pub work: Seq<Sched<InternalV>>,
    pub send: Seq<DispatchV>,
}

pub struct InOutV {
    pub next: StoreV,
    pub work: Seq<Sched<InternalV>>,
    pub send: Seq<DispatchV>,
    pub not_due: bool,
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

/// A stored schedule, as the spec holds it.
pub open spec fn schedule_v(c: Schedule) -> ScheduleV {
    ScheduleV {
        id: c.id@,
        cron: c.cron@,
        promise_id: c.promise_id@,
        promise_timeout: c.promise_timeout,
        promise_param: c.promise_param,
        promise_tags: c.promise_tags,
        created_at: c.created_at,
        next_run_at: c.next_run_at,
        last_run_at: c.last_run_at,
    }
}

impl View for Dispatch {
    type V = DispatchV;

    open spec fn view(&self) -> DispatchV {
        match self {
            Dispatch::Execute { id, version } => DispatchV::Execute { id: id@, version: *version },
            Dispatch::Unblock { address, promise } => DispatchV::Unblock { address: address@, promise: *promise },
        }
    }
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

pub broadcast proof fn lemma_strs_empty(v: Seq<String>)
    requires
        v.len() == 0,
    ensures
        #[trigger] strs(v) == Seq::<Chars>::empty(),
{
    assert(strs(v) =~= Seq::<Chars>::empty());
}

pub broadcast group group_views {
    lemma_strs_len,
    lemma_strs_index,
    lemma_strs_empty,
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

/// The version the reference kernel refuses to acquire past. This model
/// follows Lean and increments, saturating at `u64::MAX`.
pub const MAX_VERSION: u32 = u32::MAX;

pub open spec fn distinct(ids: Seq<Chars>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ids.len() ==> ids[i] != ids[j]
}

pub open spec fn all_in_origin(ids: Seq<Chars>, id: Chars) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> origin(#[trigger] ids[i]) == origin(id)
}

// ----------------------------------------------- a value for a view

pub open spec fn lift_dispatch(v: DispatchV) -> Dispatch {
    choose|x: Dispatch| x@ == v
}

/// Every dispatch view is some dispatch's view. Trusted: a string is any
/// characters, and a record is its fields.
#[verifier::external_body]
pub proof fn axiom_realised(d: DispatchV)
    ensures
        lift_dispatch(d)@ == d,
{
}

// --------------------------------------------------- a value is its view

pub proof fn lemma_prec_ext(a: PromiseRecord, b: PromiseRecord)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_record_ext(a, b);
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

pub proof fn lemma_lift_dispatch(d: Dispatch)
    ensures
        lift_dispatch(d@) == d,
{
    axiom_realised(d@);
    lemma_dispatch_ext(lift_dispatch(d@), d);
}

// ---------------------------------------------------------------------------
// The order `PMap::keys` walks: the keys of a map view, sorted
// ---------------------------------------------------------------------------

pub open spec fn spec_before(a: Seq<char>, b: Seq<char>) -> bool
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        b.len() != 0
    } else if b.len() == 0 {
        false
    } else if a[0] != b[0] {
        a[0] < b[0]
    } else {
        spec_before(a.drop_first(), b.drop_first())
    }
}

/// Opaque: the choice is read through [`lemma_min_key`] alone.
#[verifier::opaque]
pub open spec fn spec_min_key(keys: Set<Seq<char>>) -> Seq<char> {
    choose|k: Seq<char>|
        keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

/// Keys of a map in the order the store yields them: lexicographic.
pub open spec fn spec_sorted(keys: Set<Seq<char>>) -> Seq<Seq<char>>
    decreases keys.len(),
    via spec_sorted_decreases
{
    if !keys.finite() || keys.len() == 0 {
        Seq::empty()
    } else {
        let k = spec_min_key(keys);
        seq![k] + spec_sorted(keys.remove(k))
    }
}

#[via_fn]
proof fn spec_sorted_decreases(keys: Set<Seq<char>>) {
    if keys.finite() && keys.len() > 0 {
        lemma_min_key(keys);
    }
}

pub proof fn lemma_before_irrefl(a: Seq<char>)
    ensures
        !spec_before(a, a),
    decreases a.len(),
{
    if a.len() == 0 {
    } else {
        lemma_before_irrefl(a.drop_first());
    }
}

pub proof fn lemma_before_trans(a: Seq<char>, b: Seq<char>, c: Seq<char>)
    requires
        spec_before(a, b),
        spec_before(b, c),
    ensures
        spec_before(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if c.len() == 0 {
    } else if a[0] != b[0] {
    } else if b[0] != c[0] {
    } else {
        lemma_before_trans(a.drop_first(), b.drop_first(), c.drop_first());
    }
}

/// `k` is the least of `keys`.
pub open spec fn least(keys: Set<Seq<char>>, k: Seq<char>) -> bool {
    keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

/// A finite set of keys has a least key.
pub proof fn lemma_least_exists(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        exists|k: Seq<char>| least(keys, k),
    decreases keys.len(),
{
    let x = keys.choose();
    assert(keys.contains(x));
    let rest = keys.remove(x);
    assert(rest.len() == keys.len() - 1);
    if rest.len() == 0 {
        assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
            if o != x {
                assert(rest.contains(o));
            } else {
                lemma_before_irrefl(x);
            }
        };
        assert(least(keys, x));
    } else {
        lemma_least_exists(rest);
        let m = choose|m: Seq<char>| least(rest, m);
        assert(keys.contains(m));
        if spec_before(x, m) {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
                if o == x {
                    lemma_before_irrefl(x);
                } else {
                    assert(rest.contains(o));
                    if spec_before(o, x) {
                        lemma_before_trans(o, x, m);
                    }
                }
            };
            assert(least(keys, x));
        } else {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, m) by {
                if o != x {
                    assert(rest.contains(o));
                }
            };
            assert(least(keys, m));
        }
    }
}

/// The chosen minimum is a key.
pub proof fn lemma_min_key(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        keys.contains(spec_min_key(keys)),
{
    reveal(spec_min_key);
    lemma_least_exists(keys);
    let k = choose|k: Seq<char>| least(keys, k);
    assert(keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k));
}

pub open spec fn spec_keys<V>(m: Map<Seq<char>, V>) -> Seq<Seq<char>> {
    spec_sorted(m.dom())
}


} // verus!

// Primitive operations over the mathematical state.
verus! {

pub type Id = String;

/// Passive configuration read by the transition relation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Config {
    pub retry_timeout: Time,
}

impl Default for Config {
    fn default() -> Self { Config { retry_timeout: 5_000 } }
}

/// 503, shaped like the concrete node's `spec_unavailable`.
pub open spec fn spec_unavailable(request: Request) -> Response {
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => {
            spec_promise_res(503, None)
        },
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => spec_schedule_res(503, None),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => spec_status_res(503),
        Request::TaskGet(_) => spec_task_get_res(503, None),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => spec_claim_res(503, None, None),
        Request::TaskFulfill(_) => spec_promise_res(503, None),
        Request::TaskFence(_) => spec_fence_res(503, None),
    }
}

/// Tags are their strings.
pub proof fn lemma_tags_ext(a: Tags, b: Tags)
    requires
        a.deep_view() == b.deep_view(),
    ensures
        a == b,
{
    let av = a@;
    let bv = b@;
    assert(a.deep_view().len() == av.len());
    assert(b.deep_view().len() == bv.len());
    assert forall|i: int| 0 <= i < av.len() implies #[trigger] av[i] == bv[i] by {
        assert(a.deep_view()[i] == av[i].deep_view());
        assert(b.deep_view()[i] == bv[i].deep_view());
        axiom_string_ext(av[i].0, bv[i].0);
        axiom_string_ext(av[i].1, bv[i].1);
    };
    assert(av =~= bv);
    axiom_vec_ext(a, b);
}

/// A value is its view.
pub proof fn lemma_value_ext(a: Value, b: Value)
    requires
        a@ == b@,
    ensures
        a == b,
{
    assert(a@.headers == a.headers.deep_view());
    assert(b@.headers == b.headers.deep_view());
    lemma_tags_ext(a.headers, b.headers);
    match (a.data, b.data) {
        (Some(x), Some(y)) => {
            assert(x@ == y@);
            axiom_string_ext(x, y);
        },
        (None, None) => {},
        _ => {
            assert(false);
        },
    }
}

/// A schedule is its view.
pub proof fn lemma_schedule_ext(a: Schedule, b: Schedule)
    requires
        a@ == b@,
    ensures
        a == b,
{
    axiom_string_ext(a.id, b.id);
    axiom_string_ext(a.cron, b.cron);
    axiom_string_ext(a.promise_id, b.promise_id);
    lemma_value_ext(a.promise_param, b.promise_param);
    lemma_tags_ext(a.promise_tags, b.promise_tags);
}

/// A stored schedule reads back as itself.
pub proof fn lemma_schedule_value(c: Schedule)
    ensures
        spec_schedule_value(schedule_v(c)) == c,
{
    lemma_string_of(c.id);
    lemma_string_of(c.cron);
    lemma_string_of(c.promise_id);
}

/// A string is the chosen string of its characters.
pub proof fn lemma_string_of(s: String)
    ensures
        spec_string(s@) == s,
{
    reveal(spec_string);
    axiom_string_ext(spec_string(s@), s);
}

// ------------------------------------------------------------- property 1

/// created_at <= timeout_at, and if settled, created_at <= settled_at <= timeout_at.
pub open spec fn times_ok(created_at: Time, settled_at: Option<Time>, timeout_at: Time) -> bool {
    created_at <= timeout_at && match settled_at {
        Some(t) => created_at <= t && t <= timeout_at,
        None => true,
    }
}

/// Every promise record in a response has the property.
pub open spec fn response_ok(r: Response) -> bool {
    match r {
        Response::Promise(p) => match p.promise {
            Some(rec) => times_ok(rec.created_at, rec.settled_at, rec.timeout_at),
            None => true,
        },
        Response::TaskClaim(c) => match c.promise {
            Some(rec) => times_ok(rec.created_at, rec.settled_at, rec.timeout_at),
            None => true,
        },
        Response::TaskFence(f) => match f.action {
            Some(TaskFenceInnerRes::Create(p)) | Some(TaskFenceInnerRes::Settle(p)) => match p.promise {
                Some(rec) => times_ok(rec.created_at, rec.settled_at, rec.timeout_at),
                None => true,
            },
            None => true,
        },
        _ => true,
    }
}

// ---------------------------------------------------------------------------
// Tags, as a specification
// ---------------------------------------------------------------------------

pub open spec fn tag_target() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 't', 'a', 'r', 'g', 'e', 't']
}

pub open spec fn tag_timer() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 't', 'i', 'm', 'e', 'r']
}

pub open spec fn tag_external() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'e', 'x', 't', 'e', 'r', 'n', 'a', 'l']
}

pub open spec fn tag_scope() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 's', 'c', 'o', 'p', 'e']
}

pub open spec fn tag_global() -> Seq<char> {
    seq!['g', 'l', 'o', 'b', 'a', 'l']
}

pub open spec fn tag_delay() -> Seq<char> {
    seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'd', 'e', 'l', 'a', 'y']
}

pub open spec fn tag_true() -> Seq<char> {
    seq!['t', 'r', 'u', 'e']
}

pub open spec fn spec_first(tags: echod_types::Tags, key: Seq<char>, i: int) -> Option<Seq<char>>
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() {
        None
    } else if tags@[i].0@ == key {
        Some(tags@[i].1@)
    } else {
        spec_first(tags, key, i + 1)
    }
}

pub open spec fn spec_has_key(tags: echod_types::Tags, key: Seq<char>) -> bool {
    spec_first(tags, key, 0) is Some
}

pub open spec fn spec_is_timer(tags: echod_types::Tags) -> bool {
    spec_first(tags, tag_timer(), 0) == Some(tag_true())
}

pub open spec fn spec_is_external_tag(tags: echod_types::Tags) -> bool {
    spec_first(tags, tag_external(), 0) == Some(tag_true())
}

pub open spec fn spec_has_target(tags: echod_types::Tags) -> bool {
    spec_has_key(tags, tag_target())
}

pub open spec fn spec_parse_acc(s: Seq<char>, acc: u64) -> Option<u64>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(acc)
    } else if s[0] < '0' || s[0] > '9' {
        None
    } else {
        let d = (s[0] as u64) - ('0' as u64);
        if acc > (u64::MAX - d) / 10 {
            None
        } else {
            spec_parse_acc(s.drop_first(), (acc * 10 + d) as u64)
        }
    }
}

pub open spec fn spec_parse_u64(s: Seq<char>) -> Option<u64> {
    if s.len() == 0 {
        None
    } else {
        spec_parse_acc(s, 0)
    }
}

pub open spec fn spec_delay(tags: echod_types::Tags) -> Option<u64> {
    match spec_first(tags, tag_delay(), 0) {
        Some(text) => spec_parse_u64(text),
        None => None,
    }
}

pub open spec fn spec_is_global(tags: echod_types::Tags) -> bool {
    spec_first(tags, tag_scope(), 0) == Some(tag_global())
}

pub open spec fn spec_external(p: PromiseV) -> bool {
    spec_has_target(p.tags) || spec_is_global(p.tags) || spec_is_external_tag(p.tags) || spec_is_timer(p.tags)
}

/// Opaque: the choice is read through the string lemmas alone.
#[verifier::opaque]
pub open spec fn spec_string(chars: Seq<char>) -> String {
    choose|s: String| s@ == chars
}

pub open spec fn spec_opt_string(o: Option<Seq<char>>) -> Option<String> {
    match o {
        Some(s) => Some(spec_string(s)),
        None => None,
    }
}

pub open spec fn spec_empty_value() -> Value {
    Value::spec_empty()
}

// ---------------------------------------------------------------------------
// Records, as a specification
// ---------------------------------------------------------------------------

pub open spec fn spec_project_promise(p: PromiseV, now: Time) -> PromiseV {
    if p.state == PromiseState::Pending && now >= p.timeout_at {
        PromiseV {
            state: if spec_is_timer(p.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
            settled_at: Some(p.timeout_at),
            ..p
        }
    } else {
        p
    }
}

pub open spec fn spec_fulfill(t: TaskV) -> TaskV {
    TaskV {
        state: TaskState::Fulfilled,
        pid: None,
        ttl: None,
        acquired_at: 0,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_project_task(t: TaskV, promise: PromiseV) -> TaskV {
    if promise.state != PromiseState::Pending && t.state != TaskState::Fulfilled {
        spec_fulfill(t)
    } else {
        t
    }
}

pub open spec fn spec_acquire(t: TaskV, version: u64, pid: Seq<char>, ttl: Time, now: Time) -> TaskV {
    TaskV {
        state: TaskState::Acquired,
        version,
        pid: Some(pid),
        ttl: Some(ttl),
        acquired_at: now,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_unlease(t: TaskV, state: TaskState, retry: Option<Time>) -> TaskV {
    TaskV {
        state,
        pid: None,
        ttl: None,
        acquired_at: 0,
        retry_timeout_at: retry,
        ..t
    }
}

pub open spec fn spec_lease_at(t: TaskV) -> Time {
    match t.ttl {
        Some(ttl) => sat_add(t.acquired_at, ttl),
        None => t.acquired_at,
    }
}

pub open spec fn spec_resumes(n: nat) -> u64 {
    if n > u64::MAX as nat { u64::MAX } else { n as u64 }
}

pub open spec fn spec_promise_record(id: String, p: PromiseV) -> PromiseRecord {
    PromiseRecord {
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

pub open spec fn spec_task_record(id: String, t: TaskV) -> TaskRecord {
    TaskRecord {
        id,
        state: t.state,
        version: t.version,
        resumes: spec_resumes(t.resumes.len()),
        ttl: t.ttl,
        pid: spec_opt_string(t.pid),
    }
}

pub open spec fn spec_schedule_value(c: ScheduleV) -> Schedule {
    Schedule {
        id: spec_string(c.id),
        cron: spec_string(c.cron),
        promise_id: spec_string(c.promise_id),
        promise_timeout: c.promise_timeout,
        promise_param: c.promise_param,
        promise_tags: c.promise_tags,
        next_run_at: c.next_run_at,
        last_run_at: c.last_run_at,
        created_at: c.created_at,
    }
}

/// Lean's `newObject`. `at` is the birth instant, `now` is the clock.
pub open spec fn spec_new_object(
    timeout_at: Time,
    at: Time,
    now: Time,
    param: Value,
    tags: echod_types::Tags,
    runnable: bool,
) -> (PromiseV, Option<TaskV>) {
    let live_now = timeout_at > now;
    let live_at = timeout_at > at;
    let state = if live_now {
        PromiseState::Pending
    } else if spec_is_timer(tags) {
        PromiseState::Resolved
    } else {
        PromiseState::RejectedTimedout
    };
    let promise = PromiseV {
        state,
        value: spec_empty_value(),
        param,
        timeout_at,
        created_at: if live_at { at } else { timeout_at },
        settled_at: if live_now { None } else { Some(timeout_at) },
        tags,
        callbacks: Set::empty(),
        listeners: Set::empty(),
    };
    let due = match spec_delay(tags) {
        Some(d) => if d > at { d } else { at },
        None => at,
    };
    let task = if runnable {
        Some(TaskV {
            state: if live_now { TaskState::Pending } else { TaskState::Fulfilled },
            version: 0,
            pid: None,
            ttl: None,
            acquired_at: 0,
            retry_timeout_at: if live_now { Some(due) } else { None },
            resumes: Seq::empty(),
        })
    } else {
        None
    };
    (promise, task)
}

pub open spec fn spec_settle(
    s: StoreV,
    id: Seq<char>,
    state: PromiseState,
    value: Value,
    at: Time,
) -> StoreV {
    if !s.promises.contains_key(id) {
        s
    } else {
        let q = PromiseV { state, value, settled_at: Some(at), ..s.promises[id] };
        let tasks = if s.tasks.contains_key(id) && s.tasks[id].state != TaskState::Fulfilled {
            s.tasks.insert(id, spec_fulfill(s.tasks[id]))
        } else {
            s.tasks
        };
        StoreV { promises: s.promises.insert(id, q), tasks, ..s }
    }
}

pub open spec fn spec_out(resp: Response, next: StoreV) -> Seq<OutV> {
    seq![OutV { resp, next, work: Seq::empty(), send: Seq::empty() }]
}

pub open spec fn spec_promise_res(status: u16, promise: Option<PromiseRecord>) -> Response {
    Response::Promise(PromiseRes { status, promise })
}

pub open spec fn spec_schedule_res(status: u16, schedule: Option<Schedule>) -> Response {
    Response::Schedule(ScheduleRes { status, schedule })
}

pub open spec fn spec_status_res(status: u16) -> Response {
    Response::Status(StatusRes { status })
}

pub open spec fn spec_task_get_res(status: u16, task: Option<TaskRecord>) -> Response {
    Response::TaskGet(TaskGetRes { status, task })
}

pub open spec fn spec_claim_res(status: u16, task: Option<TaskRecord>, promise: Option<PromiseRecord>) -> Response {
    Response::TaskClaim(TaskClaimRes { status, task, promise })
}

pub open spec fn spec_fence_res(status: u16, action: Option<TaskFenceInnerRes>) -> Response {
    Response::TaskFence(TaskFenceRes { status, action })
}


} // verus!
