//! Mathematical state and protocol views.
//! View implementations for executable model records live in
//! `echod-abstract-exec`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use rover_spec::rover::comm::Sched;
use echod_types::{PromiseRecord, PromiseState, Response, Schedule, Tags, TaskRecord, TaskState, Value};
use super::machine::{Dispatch, Time};
use super::trusted::*;

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
