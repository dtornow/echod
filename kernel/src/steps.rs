//! The steps a node runs around a request, verified: the instant a step is
//! decided at, the single-pass normalization that fires what is due and
//! discharges what a step left owed, and the nearest deadline a document
//! owes a timer for.
//!
//! The kernel proves each handler and each internal step against the
//! catalogue; this module composes them. What it adds, and the system model
//! relies on: after a sweep at `now` nothing in the document is due at `now`
//! (`no_due`), a sweep that fired nothing left the document as it was, and
//! `next_deadline` is the least deadline of the document (`is_next`).

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use crate::commit::*;
use crate::external::*;
use crate::internal::*;
use crate::properties::*;
use crate::store::*;
use crate::store_proof::*;
use crate::tags::OType;
use crate::types::*;

verus! {

/// A document, as the kernel sees it: an origin's objects, or a schedule's
/// row. The bucket holds either kind under one protocol; which a document
/// is, its name says (`is_sched`), and the shape invariant keeps the other
/// map empty.
#[cfg(verus_keep_ghost)]
pub struct Doc {
    pub objects: Map<Seq<char>, APromise>,
    pub schedules: Map<Seq<char>, ASchedule>,
}

pub open spec fn empty_doc() -> Doc {
    Doc { objects: Map::empty(), schedules: Map::empty() }
}

/// A document as a kernel state: nothing in the outbox.
pub open spec fn full(d: Doc) -> AState {
    AState { objects: d.objects, schedules: d.schedules, outbox: Map::empty() }
}

/// A kernel state as a document: the outbox dropped.
pub open spec fn strip(s: AState) -> Doc {
    Doc { objects: s.objects, schedules: s.schedules }
}

/// A kernel state's objects alone, and its schedules alone: what a fire
/// writes to the origin's document and to the schedule's.
pub open spec fn objects_only(s: AState) -> Doc {
    Doc { objects: s.objects, schedules: Map::empty() }
}

pub open spec fn schedules_only(s: AState) -> Doc {
    Doc { objects: Map::empty(), schedules: s.schedules }
}

/// An origin's document and a schedule's, loaded together for a fire.
pub open spec fn joint(o: Doc, c: Doc) -> AState {
    AState { objects: o.objects, schedules: c.schedules, outbox: Map::empty() }
}

// ---------------------------------------------------------------------------
// Deadlines
// ---------------------------------------------------------------------------

/// A pending promise that is not internal owes a timer at its deadline.
pub open spec fn promise_deadline(p: APromise) -> Option<nat> {
    if p.state == PromiseState::Pending && p.otype() != OType::Internal { Some(p.timeout_at as nat) } else { None }
}

pub open spec fn lease_deadline(p: APromise) -> Option<nat> {
    match p.task { Some(t) => opt_nat(t.lease_timeout_at), None => None }
}

pub open spec fn retry_deadline(p: APromise) -> Option<nat> {
    match p.task { Some(t) => opt_nat(t.retry_timeout_at), None => None }
}

pub open spec fn deadline_at(p: APromise, t: nat) -> bool {
    promise_deadline(p) == Some(t) || lease_deadline(p) == Some(t) || retry_deadline(p) == Some(t)
}

pub open spec fn objects_deadline(d: Map<Seq<char>, APromise>, t: nat) -> bool {
    exists |id: Seq<char>| #[trigger] d.contains_key(id) && deadline_at(d[id], t)
}

/// A schedule owes a timer at its next run.
pub open spec fn schedules_deadline(c: Map<Seq<char>, ASchedule>, t: nat) -> bool {
    exists |id: Seq<char>| #[trigger] c.contains_key(id) && c[id].next_run_at as nat == t
}

pub open spec fn has_deadline(d: Doc, t: nat) -> bool {
    objects_deadline(d.objects, t) || schedules_deadline(d.schedules, t)
}

/// `t` is the least deadline of the document.
pub open spec fn is_next(d: Doc, t: nat) -> bool {
    has_deadline(d, t) && forall |u: nat| has_deadline(d, u) ==> t <= u
}

/// Nothing in the object is due at `now`.
pub open spec fn cleared(p: APromise, now: nat) -> bool {
    forall |t: nat| deadline_at(p, t) ==> t > now
}

pub open spec fn objects_cleared(now: nat, d: Map<Seq<char>, APromise>) -> bool {
    forall |id: Seq<char>| #[trigger] d.contains_key(id) ==> cleared(d[id], now)
}

/// Nothing in the document is due at `now`: no object, and no schedule.
pub open spec fn no_due(now: nat, d: Doc) -> bool {
    &&& objects_cleared(now, d.objects)
    &&& forall |id: Seq<char>| #[trigger] d.schedules.contains_key(id) ==> d.schedules[id].next_run_at > now
}

pub proof fn lemma_no_due(now: nat, d: Doc)
    requires no_due(now, d),
    ensures forall |t: nat| has_deadline(d, t) ==> t > now,
{
    assert forall |t: nat| has_deadline(d, t) implies t > now by {
        if objects_deadline(d.objects, t) {
            let id = choose |id: Seq<char>| #[trigger] d.objects.contains_key(id) && deadline_at(d.objects[id], t);
            assert(cleared(d.objects[id], now));
        } else {
            let id = choose |id: Seq<char>| #[trigger] d.schedules.contains_key(id) && d.schedules[id].next_run_at as nat == t;
        }
    }
}

// ---------------------------------------------------------------------------
// Kernel steps, chained
// ---------------------------------------------------------------------------

/// What post-handler normalization ensures: kernel steps at `now` that leave
/// the schedules and every object's key as they were. The system model's
/// relation for the steps after a handler or a fire.
pub open spec fn drained(now: nat, a: AState, b: AState) -> bool {
    &&& reach(now, a, b)
    &&& b.schedules == a.schedules
    &&& b.objects.dom() == a.objects.dom()
}

/// What `sweep` ensures: as `drained`, and nothing in the objects is due;
/// if nothing fired, the state is as it was.
pub open spec fn swept_by(now: nat, a: AState, b: AState, did: bool) -> bool {
    &&& drained(now, a, b)
    &&& objects_cleared(now, b.objects)
    &&& !did ==> b == a
}

/// No schedule is due at `now`: what `schedule_due` answers `None` with.
pub open spec fn schedules_idle(now: nat, c: Map<Seq<char>, ASchedule>) -> bool {
    forall |id: Seq<char>| #[trigger] c.contains_key(id) ==> c[id].next_run_at > now
}

/// One kernel step at `now`: what every handler and internal step ensures.
pub open spec fn kstep(now: nat, a: AState, b: AState) -> bool {
    inv(now, b) && legal(now, a, b)
}

/// A chain of kernel steps at `now`.
pub open spec fn chain(now: nat, s: Seq<AState>) -> bool {
    s.len() >= 1 && forall |i: int| 0 <= i < s.len() - 1 ==> #[trigger] kstep(now, s[i], s[i + 1])
}

/// `b` is what some sequence of kernel steps at `now` makes of `a`.
pub open spec fn reach(now: nat, a: AState, b: AState) -> bool {
    exists |s: Seq<AState>| #[trigger] chain(now, s) && s[0] == a && s.last() == b
}

pub proof fn lemma_reach_refl(now: nat, a: AState)
    ensures reach(now, a, a),
{
    let w: Seq<AState> = seq![a];
    assert(chain(now, w) && w[0] == a && w.last() == a);
}

pub proof fn lemma_reach_step(now: nat, a: AState, b: AState, c: AState)
    requires reach(now, a, b), kstep(now, b, c),
    ensures reach(now, a, c),
{
    let s = choose |s: Seq<AState>| #[trigger] chain(now, s) && s[0] == a && s.last() == b;
    let w = s.push(c);
    assert forall |i: int| 0 <= i < w.len() - 1 implies #[trigger] kstep(now, w[i], w[i + 1]) by {
        if i < s.len() - 1 {
            assert(kstep(now, s[i], s[i + 1]));
        } else {
            assert(w[i] == s.last());
        }
    }
    assert(chain(now, w) && w[0] == a && w.last() == c);
}

pub proof fn lemma_reach_trans(now: nat, a: AState, b: AState, c: AState)
    requires
        reach(now, a, b),
        reach(now, b, c),
    ensures
        reach(now, a, c),
{
    let x = choose |x: Seq<AState>| #[trigger] chain(now, x)
        && x[0] == a && x.last() == b;
    let y = choose |y: Seq<AState>| #[trigger] chain(now, y)
        && y[0] == b && y.last() == c;
    let z = x + y.drop_first();
    assert(z.len() >= 1);
    assert forall |i: int| 0 <= i < z.len() - 1
        implies #[trigger] kstep(now, z[i], z[i + 1]) by {
        if i < x.len() - 1 {
            assert(z[i] == x[i]);
            assert(z[i + 1] == x[i + 1]);
        } else {
            let j = i - (x.len() - 1);
            assert(0 <= j < y.len() - 1);
            if j == 0 {
                assert(z[i] == x.last());
                assert(x.last() == y[0]);
            } else {
                assert(z[i] == y[j]);
            }
            assert(z[i + 1] == y[j + 1]);
        }
    }
    assert(z[0] == a);
    assert(z.last() == c);
    assert(chain(now, z));
}

pub proof fn lemma_reach_inv(now: nat, a: AState, b: AState)
    requires reach(now, a, b), inv(now, a),
    ensures inv(now, b),
{
    let s = choose |s: Seq<AState>| #[trigger] chain(now, s) && s[0] == a && s.last() == b;
    if s.len() == 1 {
        assert(b == a);
    } else {
        let i: int = s.len() - 2;
        assert(kstep(now, s[i], s[i + 1]));
        assert(s[i + 1] == b);
    }
}

// ---------------------------------------------------------------------------
// The executable row-order specification
// ---------------------------------------------------------------------------

/// Project every promise at `now`, in stored row order.
pub open spec fn executable_deadlines(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        let a1 = executable_deadlines(a, ids.drop_last(), now);
        with_objects(
            a1,
            promise_timeout_objects(a1, ids.last(), now),
        )
    }
}

/// Reclaim every expired lease after all promise deadlines were projected.
pub open spec fn executable_leases(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        let a1 = executable_leases(a, ids.drop_last(), now);
        with_objects(
            a1,
            lease_timeout_objects(a1, ids.last(), now),
        )
    }
}

/// Apply the callback snapshot of one owed row, in stored callback order.
pub open spec fn executable_callbacks(
    a: AState,
    x: Seq<char>,
    callbacks: Seq<Seq<char>>,
    now: nat,
) -> AState
    decreases callbacks.len(),
{
    if callbacks.len() == 0 {
        a
    } else {
        callback_state(
            executable_callbacks(a, x, callbacks.drop_last(), now),
            x,
            callbacks.last(),
            now,
        )
    }
}

/// Apply the listener snapshot of one owed row, in stored listener order.
pub open spec fn executable_listeners(
    a: AState,
    x: Seq<char>,
    listeners: Seq<Seq<char>>,
    now: nat,
) -> AState
    decreases listeners.len(),
{
    if listeners.len() == 0 {
        a
    } else {
        listener_state(
            executable_listeners(a, x, listeners.drop_last(), now),
            x,
            listeners.last(),
            now,
        )
    }
}

/// The settled rows and their callback/listener lists, snapshotted after the
/// deadline and lease phases in stored row order.
pub open spec fn executable_owed_snapshot(
    a: AState,
    ids: Seq<Seq<char>>,
) -> Seq<AOwed>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        let prior = executable_owed_snapshot(a, ids.drop_last());
        let x = ids.last();
        if a.objects.contains_key(x)
            && a.objects[x].state != PromiseState::Pending
            && (a.objects[x].callbacks.len() > 0 || a.objects[x].listeners.len() > 0)
        {
            prior.push(AOwed {
                awaited: x,
                callbacks: a.objects[x].callbacks,
                listeners: a.objects[x].listeners,
            })
        } else {
            prior
        }
    }
}

/// Process every callback batch before any listener batch.
pub open spec fn executable_owed_callbacks(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
) -> AState
    decreases owed.len(),
{
    if owed.len() == 0 {
        a
    } else {
        let a1 = executable_owed_callbacks(a, owed.drop_last(), now);
        let item = owed.last();
        executable_callbacks(a1, item.awaited, item.callbacks, now)
    }
}

pub open spec fn executable_owed_listeners(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
) -> AState
    decreases owed.len(),
{
    if owed.len() == 0 {
        a
    } else {
        let a1 = executable_owed_listeners(a, owed.drop_last(), now);
        let item = owed.last();
        executable_listeners(a1, item.awaited, item.listeners, now)
    }
}

pub open spec fn executable_owed(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
) -> AState {
    let after_callbacks = executable_owed_callbacks(a, owed, now);
    executable_owed_listeners(after_callbacks, owed, now)
}

/// Retry ids snapshotted after all callbacks and listeners have run.
pub open spec fn executable_due_snapshot(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
) -> Seq<Seq<char>>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        let prior = executable_due_snapshot(a, ids.drop_last(), now);
        let x = ids.last();
        if a.objects.contains_key(x) && retry_due(a.objects[x], now) {
            prior.push(x)
        } else {
            prior
        }
    }
}

pub open spec fn executable_due(
    a: AState,
    due: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
) -> AState
    decreases due.len(),
{
    if due.len() == 0 {
        a
    } else {
        retry_timeout_state(
            executable_due(a, due.drop_last(), now, retry_timeout),
            due.last(),
            now,
            retry_timeout,
        )
    }
}

/// The exact deterministic Concrete transition inside one document:
/// deadlines, leases, all callbacks, all listeners, then retries.
pub open spec fn executable_single_pass(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
) -> AState {
    let after_deadlines = executable_deadlines(a, ids, now);
    let after_leases = executable_leases(after_deadlines, ids, now);
    let owed = executable_owed_snapshot(after_leases, ids);
    let after_owed = executable_owed(after_leases, owed, now);
    let due = executable_due_snapshot(after_owed, ids, now);
    executable_due(after_owed, due, now, retry_timeout)
}

proof fn lemma_executable_deadlines_push(
    a: AState,
    ids: Seq<Seq<char>>,
    id: Seq<char>,
    now: nat,
)
    ensures
        executable_deadlines(a, ids.push(id), now)
            == with_objects(
                executable_deadlines(a, ids, now),
                promise_timeout_objects(
                    executable_deadlines(a, ids, now),
                    id,
                    now,
                ),
            ),
{
    assert(ids.push(id).drop_last() == ids);
    assert(ids.push(id).last() == id);
}

proof fn lemma_executable_leases_push(
    a: AState,
    ids: Seq<Seq<char>>,
    id: Seq<char>,
    now: nat,
)
    ensures
        executable_leases(a, ids.push(id), now)
            == with_objects(
                executable_leases(a, ids, now),
                lease_timeout_objects(
                    executable_leases(a, ids, now),
                    id,
                    now,
                ),
            ),
{
    assert(ids.push(id).drop_last() == ids);
    assert(ids.push(id).last() == id);
}

proof fn lemma_executable_owed_snapshot_push(
    a: AState,
    ids: Seq<Seq<char>>,
    id: Seq<char>,
)
    ensures
        executable_owed_snapshot(a, ids.push(id))
            == if a.objects.contains_key(id)
                && a.objects[id].state != PromiseState::Pending
                && (a.objects[id].callbacks.len() > 0
                    || a.objects[id].listeners.len() > 0)
            {
                executable_owed_snapshot(a, ids).push(AOwed {
                    awaited: id,
                    callbacks: a.objects[id].callbacks,
                    listeners: a.objects[id].listeners,
                })
            } else {
                executable_owed_snapshot(a, ids)
            },
{
    assert(ids.push(id).drop_last() == ids);
    assert(ids.push(id).last() == id);
}

proof fn lemma_executable_callbacks_push(
    a: AState,
    x: Seq<char>,
    callbacks: Seq<Seq<char>>,
    callback: Seq<char>,
    now: nat,
)
    ensures
        executable_callbacks(a, x, callbacks.push(callback), now)
            == callback_state(
                executable_callbacks(a, x, callbacks, now),
                x,
                callback,
                now,
            ),
{
    assert(callbacks.push(callback).drop_last() == callbacks);
    assert(callbacks.push(callback).last() == callback);
}

proof fn lemma_executable_listeners_push(
    a: AState,
    x: Seq<char>,
    listeners: Seq<Seq<char>>,
    listener: Seq<char>,
    now: nat,
)
    ensures
        executable_listeners(a, x, listeners.push(listener), now)
            == listener_state(
                executable_listeners(a, x, listeners, now),
                x,
                listener,
                now,
            ),
{
    assert(listeners.push(listener).drop_last() == listeners);
    assert(listeners.push(listener).last() == listener);
}

proof fn lemma_executable_owed_callbacks_push(
    a: AState,
    owed: Seq<AOwed>,
    item: AOwed,
    now: nat,
)
    ensures
        executable_owed_callbacks(a, owed.push(item), now)
            == executable_callbacks(
                executable_owed_callbacks(a, owed, now),
                item.awaited,
                item.callbacks,
                now,
            ),
{
    assert(owed.push(item).drop_last() == owed);
    assert(owed.push(item).last() == item);
}

proof fn lemma_executable_owed_listeners_push(
    a: AState,
    owed: Seq<AOwed>,
    item: AOwed,
    now: nat,
)
    ensures
        executable_owed_listeners(a, owed.push(item), now)
            == executable_listeners(
                executable_owed_listeners(a, owed, now),
                item.awaited,
                item.listeners,
                now,
            ),
{
    assert(owed.push(item).drop_last() == owed);
    assert(owed.push(item).last() == item);
}

proof fn lemma_executable_due_snapshot_push(
    a: AState,
    ids: Seq<Seq<char>>,
    id: Seq<char>,
    now: nat,
)
    ensures
        executable_due_snapshot(a, ids.push(id), now)
            == if a.objects.contains_key(id) && retry_due(a.objects[id], now) {
                executable_due_snapshot(a, ids, now).push(id)
            } else {
                executable_due_snapshot(a, ids, now)
            },
{
    assert(ids.push(id).drop_last() == ids);
    assert(ids.push(id).last() == id);
}

proof fn lemma_executable_due_push(
    a: AState,
    due: Seq<Seq<char>>,
    id: Seq<char>,
    now: nat,
    retry_timeout: nat,
)
    ensures
        executable_due(a, due.push(id), now, retry_timeout)
            == retry_timeout_state(
                executable_due(a, due, now, retry_timeout),
                id,
                now,
                retry_timeout,
            ),
{
    assert(due.push(id).drop_last() == due);
    assert(due.push(id).last() == id);
}

proof fn lemma_executable_callbacks_frame(
    a: AState,
    x: Seq<char>,
    callbacks: Seq<Seq<char>>,
    now: nat,
)
    ensures
        executable_callbacks(a, x, callbacks, now).schedules == a.schedules,
        executable_callbacks(a, x, callbacks, now).objects.dom() == a.objects.dom(),
    decreases callbacks.len(),
{
    if callbacks.len() > 0 {
        lemma_executable_callbacks_frame(a, x, callbacks.drop_last(), now);
        let b = executable_callbacks(a, x, callbacks.drop_last(), now);
        assert(callback_state(b, x, callbacks.last(), now).schedules == b.schedules);
        assert(callback_state(b, x, callbacks.last(), now).objects.dom()
            =~= b.objects.dom());
    }
}

proof fn lemma_executable_listeners_frame(
    a: AState,
    x: Seq<char>,
    listeners: Seq<Seq<char>>,
    now: nat,
)
    ensures
        executable_listeners(a, x, listeners, now).schedules == a.schedules,
        executable_listeners(a, x, listeners, now).objects.dom() == a.objects.dom(),
    decreases listeners.len(),
{
    if listeners.len() > 0 {
        lemma_executable_listeners_frame(a, x, listeners.drop_last(), now);
        let b = executable_listeners(a, x, listeners.drop_last(), now);
        assert(listener_state(b, x, listeners.last(), now).schedules == b.schedules);
        assert(listener_state(b, x, listeners.last(), now).objects.dom()
            =~= b.objects.dom());
    }
}

proof fn lemma_executable_owed_callbacks_frame(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
)
    ensures
        executable_owed_callbacks(a, owed, now).schedules == a.schedules,
        executable_owed_callbacks(a, owed, now).objects.dom() == a.objects.dom(),
    decreases owed.len(),
{
    if owed.len() > 0 {
        lemma_executable_owed_callbacks_frame(a, owed.drop_last(), now);
        let b = executable_owed_callbacks(a, owed.drop_last(), now);
        let item = owed.last();
        lemma_executable_callbacks_frame(
            b,
            item.awaited,
            item.callbacks,
            now,
        );
    }
}

proof fn lemma_executable_owed_listeners_frame(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
)
    ensures
        executable_owed_listeners(a, owed, now).schedules == a.schedules,
        executable_owed_listeners(a, owed, now).objects.dom() == a.objects.dom(),
    decreases owed.len(),
{
    if owed.len() > 0 {
        lemma_executable_owed_listeners_frame(a, owed.drop_last(), now);
        let b = executable_owed_listeners(a, owed.drop_last(), now);
        let item = owed.last();
        lemma_executable_listeners_frame(
            b,
            item.awaited,
            item.listeners,
            now,
        );
    }
}

proof fn lemma_executable_owed_frame(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
)
    ensures
        executable_owed(a, owed, now).schedules == a.schedules,
        executable_owed(a, owed, now).objects.dom() == a.objects.dom(),
{
    lemma_executable_owed_callbacks_frame(a, owed, now);
    let b = executable_owed_callbacks(a, owed, now);
    lemma_executable_owed_listeners_frame(b, owed, now);
}

proof fn lemma_executable_due_frame(
    a: AState,
    due: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
)
    ensures
        executable_due(a, due, now, retry_timeout).schedules == a.schedules,
        executable_due(a, due, now, retry_timeout).objects.dom() == a.objects.dom(),
    decreases due.len(),
{
    if due.len() > 0 {
        lemma_executable_due_frame(
            a,
            due.drop_last(),
            now,
            retry_timeout,
        );
        let b = executable_due(a, due.drop_last(), now, retry_timeout);
        assert(retry_timeout_state(
            b,
            due.last(),
            now,
            retry_timeout,
        ).schedules == b.schedules);
        assert(retry_timeout_state(
            b,
            due.last(),
            now,
            retry_timeout,
        ).objects.dom() =~= b.objects.dom());
    }
}

// ---------------------------------------------------------------------------
// One-pass normalization leaves every object deadline ahead of `now`
// ---------------------------------------------------------------------------

pub open spec fn pass_projected(a: AState, now: nat) -> bool {
    forall |id: Seq<char>| #[trigger] a.objects.contains_key(id)
        ==> a.objects[id].project(now) == a.objects[id]
}

pub open spec fn pass_leases_clear(a: AState, now: nat) -> bool {
    forall |id: Seq<char>| #[trigger] a.objects.contains_key(id)
        ==> !lease_due(a.objects[id], now)
}

pub open spec fn pass_retries_clear(a: AState, now: nat) -> bool {
    forall |id: Seq<char>| #[trigger] a.objects.contains_key(id)
        ==> !retry_due(a.objects[id], now)
}

proof fn lemma_pass_contains_split(s: Seq<Seq<char>>, y: Seq<char>)
    requires s.len() > 0,
    ensures s.contains(y) <==> (s.drop_last().contains(y) || s.last() == y),
{
    let init = s.drop_last();
    if s.contains(y) {
        let i = choose |i: int| 0 <= i < s.len() && s[i] == y;
        if i < s.len() - 1 {
            assert(init[i] == y);
        }
    }
    if init.contains(y) {
        let i = choose |i: int| 0 <= i < init.len() && init[i] == y;
        assert(s[i] == y);
    }
    if s.last() == y {
        assert(s[s.len() - 1] == y);
    }
}

proof fn lemma_pass_insert_same(a: AState, id: Seq<char>)
    requires a.objects.contains_key(id),
    ensures with_objects(a, a.objects.insert(id, a.objects[id])) == a,
{
    assert(a.objects.insert(id, a.objects[id]) =~= a.objects);
}

proof fn lemma_pass_deadline_noop(
    a: AState,
    id: Seq<char>,
    now: nat,
)
    requires
        inv(now, a),
        !(a.objects.contains_key(id)
            && a.objects[id].state == PromiseState::Pending
            && a.objects[id].timeout_at <= now),
    ensures
        with_objects(a, promise_timeout_objects(a, id, now)) == a,
{
    if a.objects.contains_key(id) {
        let p = a.objects[id];
        if p.state == PromiseState::Pending {
            assert(p.timeout_at > now);
            assert(p.project_promise(now) == p);
            match p.task {
                None => {},
                Some(t) => {
                    assert(t.view_through(p) == t);
                },
            }
        } else {
            reveal(inv);
            assert(p.project_promise(now) == p);
            match p.task {
                None => {},
                Some(t) => {
                    assert(t.state == TaskState::Fulfilled);
                    assert(t.view_through(p) == t);
                },
            }
        }
        assert(p.project(now) == p);
        lemma_pass_insert_same(a, id);
    }
}

proof fn lemma_pass_projected_obj(p: APromise, now: nat)
    requires p.project(now) == p,
    ensures
        p.state == PromiseState::Pending ==> p.timeout_at > now,
        p.state != PromiseState::Pending && p.task is Some
            ==> p.task.unwrap().state == TaskState::Fulfilled,
{
    if p.state == PromiseState::Pending && p.timeout_at <= now {
        assert(p.project(now).state == p.project_promise(now).state);
        assert(p.project_promise(now).state != PromiseState::Pending);
        assert(false);
    }
    if p.state != PromiseState::Pending && p.task is Some {
        let t = p.task.unwrap();
        assert(p.project_promise(now) == p);
        assert(p.project(now).task == Some(t.view_through(p)));
        if t.state != TaskState::Fulfilled {
            assert(t.view_through(p).state == TaskState::Fulfilled);
            assert(false);
        }
    }
}

proof fn lemma_pass_project_lists(
    p: APromise,
    now: nat,
    callbacks: Seq<Seq<char>>,
    listeners: Seq<Seq<char>>,
)
    requires p.project(now) == p,
    ensures
        (APromise { callbacks, listeners, ..p }).project(now)
            == (APromise { callbacks, listeners, ..p }),
{
    let q = APromise { callbacks, listeners, ..p };
    lemma_pass_projected_obj(p, now);
    if p.state == PromiseState::Pending {
        assert(q.project_promise(now) == q);
        match q.task {
            None => {},
            Some(t) => {
                assert(t.view_through(q) == t);
            },
        }
    } else {
        assert(q.project_promise(now) == q);
        match q.task {
            None => {},
            Some(t) => {
                assert(t.state == TaskState::Fulfilled);
                assert(t.view_through(q) == t);
            },
        }
    }
}

proof fn lemma_pass_project_pending_task(p: APromise, now: nat, t: ATask)
    requires
        p.state == PromiseState::Pending,
        p.timeout_at > now,
    ensures p.with_task(t).project(now) == p.with_task(t),
{
    let q = p.with_task(t);
    assert(q.project_promise(now) == q);
    assert(t.view_through(q) == t);
}

proof fn lemma_pass_deadlines(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
)
    ensures
        ({
            let b = executable_deadlines(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& forall |id: Seq<char>| ids.contains(id)
                && #[trigger] a.objects.contains_key(id)
                ==> b.objects[id].project(now) == b.objects[id]
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_pass_deadlines(a, ids.drop_last(), now);
        let a1 = executable_deadlines(a, ids.drop_last(), now);
        let x = ids.last();
        let b = executable_deadlines(a, ids, now);
        if a1.objects.contains_key(x) {
            assert(b.objects == a1.objects.insert(x, a1.objects[x].project(now)));
            assert(b.objects.dom() =~= a1.objects.dom());
            crate::external_proof::lemma_project_idem(a1.objects[x], now);
        }
        assert forall |id: Seq<char>| ids.contains(id)
            && #[trigger] a.objects.contains_key(id)
            implies b.objects[id].project(now) == b.objects[id] by {
            lemma_pass_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

proof fn lemma_pass_leases(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
)
    requires pass_projected(a, now),
    ensures
        ({
            let b = executable_leases(a, ids, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& forall |id: Seq<char>| ids.contains(id)
                && #[trigger] a.objects.contains_key(id)
                ==> !lease_due(b.objects[id], now)
        }),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_pass_leases(a, ids.drop_last(), now);
        let a1 = executable_leases(a, ids.drop_last(), now);
        let x = ids.last();
        let b = executable_leases(a, ids, now);
        if a1.objects.contains_key(x) && lease_due(a1.objects[x], now) {
            let p = a1.objects[x];
            let t = p.task.unwrap().release(
                p.task.unwrap().lease_timeout_at.unwrap() as nat,
            );
            assert(b.objects == a1.objects.insert(x, p.with_task(t)));
            assert(b.objects.dom() =~= a1.objects.dom());
            lemma_pass_projected_obj(p, now);
            lemma_pass_project_pending_task(p, now, t);
            assert(!lease_due(p.with_task(t), now));
        } else {
            assert(b == a1);
        }
        assert forall |id: Seq<char>| ids.contains(id)
            && #[trigger] a.objects.contains_key(id)
            implies !lease_due(b.objects[id], now) by {
            lemma_pass_contains_split(ids, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

proof fn lemma_pass_callback(
    a: AState,
    x: Seq<char>,
    y: Seq<char>,
    now: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
    ensures
        ({
            let b = callback_state(a, x, y, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
        }),
{
    let b = callback_state(a, x, y, now);
    if a.objects.contains_key(x) {
        let p = a.objects[x].project(now);
        assert(p == a.objects[x]);
        lemma_pass_insert_same(a, x);
        let a1 = with_objects(a, a.objects.insert(x, p));
        assert(a1 == a);
        if p.state == PromiseState::Pending || !p.callbacks.contains(y) {
            assert(b == a);
        } else {
            let p2 = p.remove_callback(y);
            let a2 = with_objects(a1, a1.objects.insert(x, p2));
            assert(a2.objects.dom() =~= a.objects.dom());
            lemma_pass_project_lists(
                p,
                now,
                crate::object::without(p.callbacks, y),
                p.listeners,
            );
            assert(p2 == APromise {
                callbacks: crate::object::without(p.callbacks, y),
                listeners: p.listeners,
                ..p
            });
            assert(pass_projected(a2, now));
            assert(pass_leases_clear(a2, now));
            if !a2.objects.contains_key(y) {
                assert(b == a2);
            } else {
                let q = a2.objects[y].project(now);
                assert(q == a2.objects[y]);
                lemma_pass_insert_same(a2, y);
                let a3 = with_objects(a2, a2.objects.insert(y, q));
                assert(a3 == a2);
                match q.task {
                    None => {
                        assert(b == a3);
                    },
                    Some(t) => {
                        lemma_pass_projected_obj(q, now);
                        if t.state == TaskState::Suspended {
                            assert(q.state == PromiseState::Pending);
                            assert(y != x);
                            let t2 = t.wake(x, opt_or_zero(p.settled_at));
                            lemma_pass_project_pending_task(q, now, t2);
                            assert(b == with_objects(
                                a3,
                                a3.objects.insert(y, q.with_task(t2)),
                            ));
                            assert(b.objects.dom() =~= a.objects.dom());
                            assert(!lease_due(q.with_task(t2), now));
                        } else if t.state != TaskState::Fulfilled {
                            assert(q.state == PromiseState::Pending);
                            assert(y != x);
                            let t2 = t.buffer(x);
                            lemma_pass_project_pending_task(q, now, t2);
                            assert(b == with_objects(
                                a3,
                                a3.objects.insert(y, q.with_task(t2)),
                            ));
                            assert(b.objects.dom() =~= a.objects.dom());
                            assert(!lease_due(q.with_task(t2), now));
                        } else {
                            assert(b == a3);
                        }
                    },
                }
            }
        }
    } else {
        assert(b == a);
    }
}

proof fn lemma_pass_callbacks(
    a: AState,
    x: Seq<char>,
    callbacks: Seq<Seq<char>>,
    now: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
    ensures
        ({
            let b = executable_callbacks(a, x, callbacks, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
        }),
    decreases callbacks.len(),
{
    if callbacks.len() > 0 {
        lemma_pass_callbacks(a, x, callbacks.drop_last(), now);
        lemma_pass_callback(
            executable_callbacks(a, x, callbacks.drop_last(), now),
            x,
            callbacks.last(),
            now,
        );
    }
}

proof fn lemma_pass_owed_callbacks(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
    ensures
        ({
            let b = executable_owed_callbacks(a, owed, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
        }),
    decreases owed.len(),
{
    if owed.len() > 0 {
        lemma_pass_owed_callbacks(a, owed.drop_last(), now);
        let a1 = executable_owed_callbacks(a, owed.drop_last(), now);
        let item = owed.last();
        lemma_pass_callbacks(a1, item.awaited, item.callbacks, now);
    }
}

proof fn lemma_pass_listener(
    a: AState,
    x: Seq<char>,
    address: Seq<char>,
    now: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
    ensures
        ({
            let b = listener_state(a, x, address, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
        }),
{
    let b = listener_state(a, x, address, now);
    if a.objects.contains_key(x) {
        let p = a.objects[x].project(now);
        assert(p == a.objects[x]);
        lemma_pass_insert_same(a, x);
        let a1 = with_objects(a, a.objects.insert(x, p));
        assert(a1 == a);
        if p.state == PromiseState::Pending || !p.listeners.contains(address) {
            assert(b == a);
        } else {
            let q = p.remove_listener(address);
            assert(b.objects == a.objects.insert(x, q));
            assert(b.objects.dom() =~= a.objects.dom());
            lemma_pass_project_lists(
                p,
                now,
                p.callbacks,
                crate::object::without(p.listeners, address),
            );
            assert(q == APromise {
                callbacks: p.callbacks,
                listeners: crate::object::without(p.listeners, address),
                ..p
            });
        }
    } else {
        assert(b == a);
    }
}

proof fn lemma_pass_listeners(
    a: AState,
    x: Seq<char>,
    listeners: Seq<Seq<char>>,
    now: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
    ensures
        ({
            let b = executable_listeners(a, x, listeners, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
        }),
    decreases listeners.len(),
{
    if listeners.len() > 0 {
        lemma_pass_listeners(a, x, listeners.drop_last(), now);
        lemma_pass_listener(
            executable_listeners(a, x, listeners.drop_last(), now),
            x,
            listeners.last(),
            now,
        );
    }
}

proof fn lemma_pass_owed_listeners(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
    ensures
        ({
            let b = executable_owed_listeners(a, owed, now);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
        }),
    decreases owed.len(),
{
    if owed.len() > 0 {
        lemma_pass_owed_listeners(a, owed.drop_last(), now);
        let a1 = executable_owed_listeners(a, owed.drop_last(), now);
        let item = owed.last();
        lemma_pass_listeners(a1, item.awaited, item.listeners, now);
    }
}

proof fn lemma_pass_due_snapshot_contains(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
    id: Seq<char>,
)
    ensures
        executable_due_snapshot(a, ids, now).contains(id)
            <==> ids.contains(id)
                && a.objects.contains_key(id)
                && retry_due(a.objects[id], now),
    decreases ids.len(),
{
    if ids.len() > 0 {
        lemma_pass_due_snapshot_contains(a, ids.drop_last(), now, id);
        lemma_pass_contains_split(ids, id);
        let x = ids.last();
        if a.objects.contains_key(x) && retry_due(a.objects[x], now) {
            assert(executable_due_snapshot(a, ids, now)
                == executable_due_snapshot(a, ids.drop_last(), now).push(x));
            assert(executable_due_snapshot(a, ids, now).contains(id)
                <==> executable_due_snapshot(a, ids.drop_last(), now).contains(id)
                    || x == id) by {
                let due = executable_due_snapshot(a, ids.drop_last(), now);
                if due.push(x).contains(id) {
                    let i = choose |i: int| 0 <= i < due.push(x).len()
                        && due.push(x)[i] == id;
                    if i < due.len() {
                        assert(due[i] == id);
                    }
                }
                if due.contains(id) {
                    let i = choose |i: int| 0 <= i < due.len()
                        && due[i] == id;
                    assert(due.push(x)[i] == id);
                }
                if x == id {
                    assert(due.push(x)[due.len() as int] == id);
                }
            }
        }
    }
}

proof fn lemma_pass_retry(
    a: AState,
    id: Seq<char>,
    now: nat,
    retry_timeout: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
        0 < retry_timeout <= MAX_TIME,
        now <= MAX_TIME,
    ensures
        ({
            let b = retry_timeout_state(a, id, now, retry_timeout);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
            &&& forall |z: Seq<char>| #[trigger] a.objects.contains_key(z)
                && z != id ==> b.objects[z] == a.objects[z]
            &&& a.objects.contains_key(id) ==> !retry_due(b.objects[id], now)
        }),
{
    let b = retry_timeout_state(a, id, now, retry_timeout);
    if a.objects.contains_key(id) && retry_due(a.objects[id], now) {
        let p = a.objects[id];
        let t0 = p.task.unwrap();
        let due = opt_or_zero(t0.retry_timeout_at);
        assert(due == t0.retry_timeout_at.unwrap() as nat);
        assert(due <= now);
        crate::object::lemma_next_offer(due, now, retry_timeout);
        let n = crate::object::next_offer(due, now, retry_timeout);
        assert(now < n <= now + retry_timeout);
        assert(now + retry_timeout <= 2 * (MAX_TIME as nat));
        assert(now + retry_timeout <= u64::MAX);
        assert(n as u64 == n);
        let t2 = t0.rearm(now, retry_timeout);
        assert(t2.retry_timeout_at == Some(n as u64));
        assert(b.objects == a.objects.insert(id, p.with_task(t2)));
        assert(b.objects.dom() =~= a.objects.dom());
        lemma_pass_project_pending_task(p, now, t2);
        assert(!lease_due(p.with_task(t2), now));
        assert(!retry_due(p.with_task(t2), now));
    } else {
        assert(b == a);
    }
}

proof fn lemma_pass_due(
    a: AState,
    due: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
)
    requires
        pass_projected(a, now),
        pass_leases_clear(a, now),
        0 < retry_timeout <= MAX_TIME,
        now <= MAX_TIME,
    ensures
        ({
            let b = executable_due(a, due, now, retry_timeout);
            &&& b.objects.dom() == a.objects.dom()
            &&& b.schedules == a.schedules
            &&& pass_projected(b, now)
            &&& pass_leases_clear(b, now)
            &&& forall |id: Seq<char>| !due.contains(id)
                && #[trigger] a.objects.contains_key(id)
                ==> b.objects[id] == a.objects[id]
            &&& forall |id: Seq<char>| due.contains(id)
                && #[trigger] a.objects.contains_key(id)
                ==> !retry_due(b.objects[id], now)
        }),
    decreases due.len(),
{
    if due.len() > 0 {
        lemma_pass_due(a, due.drop_last(), now, retry_timeout);
        let a1 = executable_due(a, due.drop_last(), now, retry_timeout);
        let x = due.last();
        lemma_pass_retry(a1, x, now, retry_timeout);
        let b = executable_due(a, due, now, retry_timeout);
        assert(b == retry_timeout_state(a1, x, now, retry_timeout));
        assert forall |id: Seq<char>| !due.contains(id)
            && #[trigger] a.objects.contains_key(id)
            implies b.objects[id] == a.objects[id] by {
            lemma_pass_contains_split(due, id);
            assert(id != x);
            assert(b.objects[id] == a1.objects[id]);
        }
        assert forall |id: Seq<char>| due.contains(id)
            && #[trigger] a.objects.contains_key(id)
            implies !retry_due(b.objects[id], now) by {
            lemma_pass_contains_split(due, id);
            if id != x {
                assert(b.objects[id] == a1.objects[id]);
            }
        }
    }
}

proof fn lemma_single_pass_cleared(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
)
    requires
        object_order(a, ids),
        inv(now, executable_single_pass(a, ids, now, retry_timeout)),
        0 < retry_timeout <= MAX_TIME,
        now <= MAX_TIME,
    ensures
        objects_cleared(
            now,
            executable_single_pass(a, ids, now, retry_timeout).objects,
        ),
        executable_single_pass(a, ids, now, retry_timeout).objects.dom()
            == a.objects.dom(),
        executable_single_pass(a, ids, now, retry_timeout).schedules
            == a.schedules,
{
    let a1 = executable_deadlines(a, ids, now);
    let a2 = executable_leases(a1, ids, now);
    let owed = executable_owed_snapshot(a2, ids);
    let a3 = executable_owed_callbacks(a2, owed, now);
    let a4 = executable_owed_listeners(a3, owed, now);
    let due = executable_due_snapshot(a4, ids, now);
    let a5 = executable_due(a4, due, now, retry_timeout);

    lemma_pass_deadlines(a, ids, now);
    assert(pass_projected(a1, now)) by {
        assert forall |id: Seq<char>| #[trigger] a1.objects.contains_key(id)
            implies a1.objects[id].project(now) == a1.objects[id] by {
            assert(a.objects.contains_key(id));
            assert(ids.contains(id));
        }
    }
    lemma_pass_leases(a1, ids, now);
    assert(pass_leases_clear(a2, now)) by {
        assert forall |id: Seq<char>| #[trigger] a2.objects.contains_key(id)
            implies !lease_due(a2.objects[id], now) by {
            assert(a.objects.contains_key(id));
            assert(a1.objects.contains_key(id));
            assert(ids.contains(id));
        }
    }
    lemma_pass_owed_callbacks(a2, owed, now);
    lemma_pass_owed_listeners(a3, owed, now);
    lemma_pass_due(a4, due, now, retry_timeout);
    assert(pass_retries_clear(a5, now)) by {
        assert forall |id: Seq<char>| #[trigger] a5.objects.contains_key(id)
            implies !retry_due(a5.objects[id], now) by {
            assert(a.objects.contains_key(id));
            assert(a4.objects.contains_key(id));
            assert(ids.contains(id));
            lemma_pass_due_snapshot_contains(a4, ids, now, id);
            if retry_due(a4.objects[id], now) {
                assert(due.contains(id));
            } else {
                assert(!due.contains(id));
                assert(a5.objects[id] == a4.objects[id]);
            }
        }
    }

    assert(a5 == executable_single_pass(a, ids, now, retry_timeout));
    reveal(inv);
    assert forall |id: Seq<char>| #[trigger] a5.objects.contains_key(id)
        implies cleared(a5.objects[id], now) by {
        let p = a5.objects[id];
        lemma_pass_projected_obj(p, now);
        assert forall |t: nat| deadline_at(p, t) implies t > now by {
            if promise_deadline(p) == Some(t) {
                assert(t == p.timeout_at as nat);
            } else if lease_deadline(p) == Some(t) {
                let task = p.task.unwrap();
                assert(task.lease_timeout_at is Some);
                assert(t == task.lease_timeout_at.unwrap() as nat);
                assert(task.state == TaskState::Acquired);
                if p.state != PromiseState::Pending {
                    assert(task.state == TaskState::Fulfilled);
                    assert(false);
                }
                if t <= now {
                    assert(lease_due(p, now));
                    assert(false);
                }
            } else {
                let task = p.task.unwrap();
                assert(task.retry_timeout_at is Some);
                assert(t == task.retry_timeout_at.unwrap() as nat);
                assert(task.state == TaskState::Pending);
                if p.state != PromiseState::Pending {
                    assert(task.state == TaskState::Fulfilled);
                    assert(false);
                }
                if t <= now {
                    assert(retry_due(p, now));
                    assert(false);
                }
            }
        }
    }
}

/// The catalogue at a later instant. Three entries mention `now`: two say
/// the stamps are not in the future, one that a suspended task holds a
/// rung unless its promise is dead; none is lost as time passes.
pub proof fn lemma_inv_at(t0: nat, t: nat, s: AState)
    requires
        inv(t0, s),
        t0 <= t,
    ensures inv(t, s),
{
    reveal(inv);
    assert(well_formed_promise_created_at_lte_timeout_at(t, s)) by { assert(well_formed_promise_created_at_lte_timeout_at(t0, s)); }
    assert(well_formed_promise_pending_created_before_deadline(t, s)) by { assert(well_formed_promise_pending_created_before_deadline(t0, s)); }
    assert(well_formed_promise_settled_at_lte_timeout_at(t, s)) by { assert(well_formed_promise_settled_at_lte_timeout_at(t0, s)); }
    assert(well_formed_promise_created_at_lte_settled_at(t, s)) by { assert(well_formed_promise_created_at_lte_settled_at(t0, s)); }
    assert(well_formed_promise_settled_at_iff_not_pending(t, s)) by { assert(well_formed_promise_settled_at_iff_not_pending(t0, s)); }
    assert(well_formed_promise_pending_has_no_value(t, s)) by { assert(well_formed_promise_pending_has_no_value(t0, s)); }
    assert(well_formed_promise_deadline_verdict_matches_timer_tag(t, s)) by { assert(well_formed_promise_deadline_verdict_matches_timer_tag(t0, s)); }
    assert(well_formed_promise_deadline_settlement_has_no_value(t, s)) by { assert(well_formed_promise_deadline_settlement_has_no_value(t0, s)); }
    assert(well_formed_promise_timer_not_targeted(t, s)) by { assert(well_formed_promise_timer_not_targeted(t0, s)); }
    assert(well_formed_promise_timedout_is_server_owned(t, s)) by { assert(well_formed_promise_timedout_is_server_owned(t0, s)); }
    assert(well_formed_promise_callbacks_unique(t, s)) by { assert(well_formed_promise_callbacks_unique(t0, s)); }
    assert(well_formed_promise_listeners_unique(t, s)) by { assert(well_formed_promise_listeners_unique(t0, s)); }
    assert(well_formed_promise_obligations_require_external(t, s)) by { assert(well_formed_promise_obligations_require_external(t0, s)); }
    assert(well_formed_promise_awaiter_is_not_self(t, s)) by { assert(well_formed_promise_awaiter_is_not_self(t0, s)); }
    assert(well_formed_promise_callbacks_same_origin(t, s)) by { assert(well_formed_promise_callbacks_same_origin(t0, s)); }
    assert(well_formed_promise_created_at_lte_now(t, s)) by { assert(well_formed_promise_created_at_lte_now(t0, s)); }
    assert(well_formed_promise_settled_at_lte_now(t, s)) by { assert(well_formed_promise_settled_at_lte_now(t0, s)); }
    assert(well_formed_task_acquired_iff_has_pid(t, s)) by { assert(well_formed_task_acquired_iff_has_pid(t0, s)); }
    assert(well_formed_task_acquired_iff_has_ttl(t, s)) by { assert(well_formed_task_acquired_iff_has_ttl(t0, s)); }
    assert(well_formed_task_acquired_iff_has_lease_timeout_at(t, s)) by { assert(well_formed_task_acquired_iff_has_lease_timeout_at(t0, s)); }
    assert(well_formed_task_pending_iff_has_retry_timeout_at(t, s)) by { assert(well_formed_task_pending_iff_has_retry_timeout_at(t0, s)); }
    assert(well_formed_task_fulfilled_is_cleared(t, s)) by { assert(well_formed_task_fulfilled_is_cleared(t0, s)); }
    assert(well_formed_task_suspended_is_cleared(t, s)) by { assert(well_formed_task_suspended_is_cleared(t0, s)); }
    assert(well_formed_task_halted_is_cleared(t, s)) by { assert(well_formed_task_halted_is_cleared(t0, s)); }
    assert(well_formed_task_suspended_has_no_resumes(t, s)) by { assert(well_formed_task_suspended_has_no_resumes(t0, s)); }
    assert(well_formed_task_resumes_unique(t, s)) by { assert(well_formed_task_resumes_unique(t0, s)); }
    assert(well_formed_task_acquired_version_positive(t, s)) by { assert(well_formed_task_acquired_version_positive(t0, s)); }
    assert(well_formed_schedule_promise_tags_not_timer_targeted(t, s)) by { assert(well_formed_schedule_promise_tags_not_timer_targeted(t0, s)); }
    assert(well_formed_schedule_created_at_lte_next_run_at(t, s)) by { assert(well_formed_schedule_created_at_lte_next_run_at(t0, s)); }
    assert(well_formed_schedule_created_at_lte_last_run_at(t, s)) by { assert(well_formed_schedule_created_at_lte_last_run_at(t0, s)); }
    assert(well_formed_schedule_last_run_at_lt_next_run_at(t, s)) by { assert(well_formed_schedule_last_run_at_lt_next_run_at(t0, s)); }
    assert(consistent_task_iff_kind_task(t, s)) by { assert(consistent_task_iff_kind_task(t0, s)); }
    assert(consistent_settled_promise_has_fulfilled_task(t, s)) by { assert(consistent_settled_promise_has_fulfilled_task(t0, s)); }
    assert(consistent_callback_awaiter_is_targeted(t, s)) by { assert(consistent_callback_awaiter_is_targeted(t0, s)); }
    assert(consistent_outbox_execute_names_existing_task(t, s)) by { assert(consistent_outbox_execute_names_existing_task(t0, s)); }
    assert(consistent_outbox_never_ahead(t, s)) by { assert(consistent_outbox_never_ahead(t0, s)); }
    assert(consistent_outbox_execute_address_is_target_tag(t, s)) by { assert(consistent_outbox_execute_address_is_target_tag(t0, s)); }
    assert(consistent_outbox_unblock_names_settled_promise(t, s)) by { assert(consistent_outbox_unblock_names_settled_promise(t0, s)); }
    assert(consistent_settled_task_promise_settled(t, s)) by { assert(consistent_settled_task_promise_settled(t0, s)); }
    assert(consistent_suspended_task_holds_rung(t, s)) by {
        assert forall |id: Seq<char>| #[trigger] s.objects.contains_key(id) implies consistent_suspended_task_holds_rung_at(t, s, id) by {
            assert(consistent_suspended_task_holds_rung_at(t0, s, id));
            let p = s.objects[id];
            if p.project_promise(t0).state != PromiseState::Pending {
                assert(p.project_promise(t).state != PromiseState::Pending);
            }
        }
    }
}

/// The catalogue on the objects alone.
pub proof fn lemma_inv_full(now: nat, s: AState)
    requires inv(now, s),
    ensures inv(now, full(strip(s))),
{
    reveal(inv);
}

/// The catalogue holds of a state's objects alone, and of its schedules
/// alone: no entry crosses from one to the other.
pub proof fn lemma_inv_objects_only(now: nat, s: AState)
    requires inv(now, s),
    ensures inv(now, full(objects_only(s))),
{
    reveal(inv);
}

pub proof fn lemma_inv_schedules_only(now: nat, s: AState)
    requires inv(now, s),
    ensures inv(now, full(schedules_only(s))),
{
    reveal(inv);
}

/// And of an origin's objects beside a schedule's row.
pub proof fn lemma_inv_joint(now: nat, o: Doc, c: Doc)
    requires inv(now, full(o)), inv(now, full(c)), o.schedules == Map::<Seq<char>, ASchedule>::empty(), c.objects == Map::<Seq<char>, APromise>::empty(),
    ensures inv(now, joint(o, c)),
{
    reveal(inv);
}

// ---------------------------------------------------------------------------
// The instant a step is decided at
// ---------------------------------------------------------------------------

/// The instant a step on a document is decided at: the node's clock, or the
/// document's stamp — the instant of the step that wrote it — whichever is
/// later. The kernel is proved for `now` at or after the instant it last
/// ran at (`lemma_inv_at`), and a node behind the previous writer's clock
/// would otherwise step outside that.
pub fn clamp_now(stamp: u64, now: u64) -> (r: u64)
    ensures r >= stamp, r >= now, r == stamp || r == now,
{
    if stamp > now { stamp } else { now }
}

// ---------------------------------------------------------------------------
// The nearest deadline
// ---------------------------------------------------------------------------

fn note(min: Option<u64>, d: u64) -> (r: Option<u64>)
    ensures r == Some(match min { Some(m) => if d < m { d } else { m }, None => d }),
{
    match min {
        Some(m) => if d < m { Some(d) } else { Some(m) },
        None => Some(d),
    }
}

/// The least deadline of the object rows, which fold to the objects.
fn objects_next(rows: &Vec<Promise>) -> (r: Option<u64>)
    requires distinct_by(rows@, obj_key()),
    ensures
        match r {
            Some(d) => objects_deadline(fold_by(rows@, obj_key(), obj_val()), d as nat)
                && forall |u: nat| objects_deadline(fold_by(rows@, obj_key(), obj_val()), u) ==> d as nat <= u,
            None => forall |t: nat| !objects_deadline(fold_by(rows@, obj_key(), obj_val()), t),
        },
{
    let mut min: Option<u64> = None;
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows@.len(),
            match min {
                Some(m) => (exists |j: int| 0 <= j < i && #[trigger] deadline_at(rows@[j]@, m as nat))
                    && forall |j: int, t: nat| 0 <= j < i && #[trigger] deadline_at(rows@[j]@, t) ==> m as nat <= t,
                None => forall |j: int, t: nat| 0 <= j < i ==> !#[trigger] deadline_at(rows@[j]@, t),
            },
        decreases rows@.len() - i,
    {
        let p = &rows[i];
        let ghost before = min;
        let ghost ap = p@;
        let pending = match p.state { PromiseState::Pending => true, _ => false };
        let internal = match crate::tags::exec_otype(&p.tags) { OType::Internal => true, _ => false };
        if pending && !internal {
            min = note(min, p.timeout_at);
        }
        let ghost after_p = min;
        match &p.task {
            Some(t) => {
                match t.lease_timeout_at {
                    Some(d) => { min = note(min, d); }
                    None => {}
                }
                match t.retry_timeout_at {
                    Some(d) => { min = note(min, d); }
                    None => {}
                }
            }
            None => {}
        }
        proof {
            assert(promise_deadline(ap) == (if pending && !internal { Some(ap.timeout_at as nat) } else { None }));
            assert forall |t: nat| deadline_at(ap, t) implies min is Some && min.unwrap() as nat <= t by {}
            assert forall |j: int, t: nat| 0 <= j < i + 1 && #[trigger] deadline_at(rows@[j]@, t) implies min is Some && min.unwrap() as nat <= t by {
                if j < i {
                    assert(deadline_at(rows@[j]@, t));
                }
            }
            if min is Some {
                let m = min.unwrap() as nat;
                if before is Some && m == before.unwrap() as nat {
                    let j = choose |j: int| 0 <= j < i && deadline_at(#[trigger] rows@[j]@, m);
                    assert(deadline_at(rows@[j]@, m));
                } else {
                    assert(deadline_at(rows@[i as int]@, m));
                }
            }
        }
        i += 1;
    }
    proof {
        let d = fold_by(rows@, obj_key(), obj_val());
        lemma_fold_dom(rows@, obj_key(), obj_val());
        lemma_fold_distinct(rows@, obj_key(), obj_val());
        assert forall |t: nat| objects_deadline(d, t) implies exists |j: int| 0 <= j < rows@.len() && #[trigger] deadline_at(rows@[j]@, t) by {
            let id = choose |id: Seq<char>| #[trigger] d.contains_key(id) && deadline_at(d[id], t);
            assert(mentions(rows@, obj_key(), id));
            let j = choose |j: int| 0 <= j < rows@.len() && #[trigger] obj_key()(rows@[j]) == id;
            assert(d[obj_key()(rows@[j])] == obj_val()(rows@[j]));
            assert(deadline_at(rows@[j]@, t));
        }
        assert forall |j: int, t: nat| 0 <= j < rows@.len() && #[trigger] deadline_at(rows@[j]@, t) implies objects_deadline(d, t) by {
            assert(d.contains_key(obj_key()(rows@[j])));
            assert(d[obj_key()(rows@[j])] == obj_val()(rows@[j]));
        }
    }
    min
}

/// The least next run of the schedule rows, which fold to the schedules.
fn schedules_next(rows: &Vec<Schedule>) -> (r: Option<u64>)
    requires distinct_by(rows@, sched_key()),
    ensures
        match r {
            Some(d) => schedules_deadline(fold_by(rows@, sched_key(), sched_val()), d as nat)
                && forall |u: nat| schedules_deadline(fold_by(rows@, sched_key(), sched_val()), u) ==> d as nat <= u,
            None => forall |t: nat| !schedules_deadline(fold_by(rows@, sched_key(), sched_val()), t),
        },
{
    let mut min: Option<u64> = None;
    let mut i: usize = 0;
    while i < rows.len()
        invariant
            i <= rows@.len(),
            match min {
                Some(m) => (exists |j: int| 0 <= j < i && #[trigger] rows@[j].next_run_at == m)
                    && forall |j: int| 0 <= j < i ==> m <= #[trigger] rows@[j].next_run_at,
                None => i == 0,
            },
        decreases rows@.len() - i,
    {
        let ghost before = min;
        min = note(min, rows[i].next_run_at);
        proof {
            if before is Some && min == before {
                let j = choose |j: int| 0 <= j < i && #[trigger] rows@[j].next_run_at == before.unwrap();
                assert(rows@[j].next_run_at == min.unwrap());
            } else {
                assert(rows@[i as int].next_run_at == min.unwrap());
            }
        }
        i += 1;
    }
    proof {
        let c = fold_by(rows@, sched_key(), sched_val());
        lemma_fold_dom(rows@, sched_key(), sched_val());
        lemma_fold_distinct(rows@, sched_key(), sched_val());
        assert forall |t: nat| schedules_deadline(c, t) implies exists |j: int| 0 <= j < rows@.len() && #[trigger] rows@[j].next_run_at as nat == t by {
            let id = choose |id: Seq<char>| #[trigger] c.contains_key(id) && c[id].next_run_at as nat == t;
            assert(mentions(rows@, sched_key(), id));
            let j = choose |j: int| 0 <= j < rows@.len() && #[trigger] sched_key()(rows@[j]) == id;
            assert(c[sched_key()(rows@[j])] == sched_val()(rows@[j]));
            assert(rows@[j].next_run_at as nat == t);
        }
        assert forall |j: int| 0 <= j < rows@.len() implies schedules_deadline(c, #[trigger] rows@[j].next_run_at as nat) by {
            assert(c.contains_key(sched_key()(rows@[j])));
            assert(c[sched_key()(rows@[j])] == sched_val()(rows@[j]));
        }
    }
    min
}

/// A schedule due at `now`, if any: the first row whose next run has come.
/// A fire's decision: `None` is a schedule's document with nothing due,
/// which is swept unchanged so its key can be collected.
pub fn schedule_due(s: &State, now: u64) -> (r: Option<usize>)
    requires s.wf(),
    ensures
        match r {
            Some(i) => i < s.schedules@.len() && s.schedules@[i as int].next_run_at <= now
                && s@.schedules.contains_key(s.schedules@[i as int].id@) && s@.schedules[s.schedules@[i as int].id@] == s.schedules@[i as int]@,
            None => schedules_idle(now as nat, s@.schedules),
        },
{
    let mut i: usize = 0;
    while i < s.schedules.len()
        invariant
            s.wf(),
            i <= s.schedules@.len(),
            forall |j: int| 0 <= j < i ==> #[trigger] s.schedules@[j].next_run_at > now,
        decreases s.schedules@.len() - i,
    {
        if s.schedules[i].next_run_at <= now {
            proof { s.lemma_schedule_at(i as int); }
            return Some(i);
        }
        i += 1;
    }
    proof {
        let c = fold_by(s.schedules@, sched_key(), sched_val());
        lemma_fold_dom(s.schedules@, sched_key(), sched_val());
        lemma_fold_distinct(s.schedules@, sched_key(), sched_val());
        assert forall |id: Seq<char>| #[trigger] c.contains_key(id) implies c[id].next_run_at > now by {
            assert(mentions(s.schedules@, sched_key(), id));
            let j = choose |j: int| 0 <= j < s.schedules@.len() && #[trigger] sched_key()(s.schedules@[j]) == id;
            assert(c[sched_key()(s.schedules@[j])] == sched_val()(s.schedules@[j]));
        }
    }
    None
}

/// The least deadline of a state: of its objects and of its schedules.
pub fn next_deadline(s: &State) -> (r: Option<u64>)
    requires s.wf(),
    ensures
        match r {
            Some(d) => is_next(strip(s@), d as nat),
            None => forall |t: nat| !has_deadline(strip(s@), t),
        },
{
    let a = objects_next(&s.objects);
    let b = schedules_next(&s.schedules);
    let r = match (a, b) {
        (None, None) => None,
        (Some(x), None) => Some(x),
        (None, Some(y)) => Some(y),
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    };
    proof {
        let d = strip(s@);
        assert(d.objects == fold_by(s.objects@, obj_key(), obj_val()));
        assert(d.schedules == fold_by(s.schedules@, sched_key(), sched_val()));
    }
    r
}

// ---------------------------------------------------------------------------
// The sweep
// ---------------------------------------------------------------------------

/// Normalize a document at `now` in one topological pass: all promise
/// deadlines, all leases, all callbacks, all listeners, then all retries.
pub fn sweep(s: &mut State, now: u64, cfg: &Config) -> (did: bool)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        swept_by(now as nat, old(s)@, final(s)@, did),
        object_ids(*final(s)) == object_ids(*old(s)),
        final(s)@ == executable_single_pass(
            old(s)@,
            object_ids(*old(s)),
            now as nat,
            cfg.retry_timeout as nat,
        ),
{
    let ghost a = s@;
    proof { s.lemma_object_order(); }
    let ids = clone_object_ids(s);
    let d1 = apply_deadlines(s, &ids, now, cfg);
    let ghost after_deadlines = s@;
    let d2 = apply_leases(s, &ids, now, cfg);
    let ghost after_leases = s@;
    let owed = snapshot_owed(s);
    let d3 = !owed.is_empty();
    apply_owed(s, &owed, now, cfg);
    let ghost after_owed = s@;
    let due = snapshot_due(s, now);
    let d4 = !due.is_empty();
    apply_due(s, &due, now, cfg);
    proof {
        lemma_reach_trans(now as nat, a, after_deadlines, after_leases);
        lemma_reach_trans(now as nat, a, after_leases, after_owed);
        lemma_reach_trans(now as nat, a, after_owed, s@);
        lemma_single_pass_cleared(
            a,
            ids.deep_view(),
            now as nat,
            cfg.retry_timeout as nat,
        );
        assert(s@ == executable_single_pass(
            a,
            ids.deep_view(),
            now as nat,
            cfg.retry_timeout as nat,
        ));
        assert(objects_cleared(now as nat, s@.objects));
        assert(s@.schedules == a.schedules);
        assert(s@.objects.dom() == a.objects.dom());
        if !(d1 || d2 || d3 || d4) {
            assert(after_deadlines == a);
            assert(after_leases == after_deadlines);
            assert(owed.deep_view().len() == 0);
            assert(after_owed == after_leases);
            assert(due.deep_view().len() == 0);
            assert(s@ == after_owed);
            assert(s@ == a);
        }
        assert(swept_by(
            now as nat,
            a,
            s@,
            d1 || d2 || d3 || d4,
        ));
    }
    d1 || d2 || d3 || d4
}

// ---------------------------------------------------------------------------
// The single-pass executable normalization
// ---------------------------------------------------------------------------

/// What a settled promise still owes: its callbacks and listeners.
#[make_spec_type]
pub struct Owed {
    pub awaited: String,
    pub callbacks: Vec<String>,
    pub listeners: Vec<String>,
}

#[cfg(verus_keep_ghost)]
pub type AOwed = OwedSpec;

fn clone_strings(v: &Vec<String>) -> (r: Vec<String>)
    ensures r.deep_view() == v.deep_view(),
{
    let mut r: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@.len() == i, forall |j: int| 0 <= j < i ==> #[trigger] r@[j]@ == v@[j]@,
        decreases v@.len() - i,
    {
        r.push(clone_string(&v[i]));
        i += 1;
    }
    assert(r.deep_view() =~= v.deep_view());
    r
}

fn clone_object_ids(s: &State) -> (ids: Vec<String>)
    ensures ids.deep_view() == object_ids(*s),
{
    let mut ids: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < s.objects.len()
        invariant
            i <= s.objects@.len(),
            ids@.len() == i,
            forall |j: int| 0 <= j < i
                ==> #[trigger] ids@[j]@ == s.objects@[j].id@,
        decreases s.objects@.len() - i,
    {
        ids.push(clone_string(&s.objects[i].id));
        i += 1;
    }
    assert(ids.deep_view() =~= object_ids(*s));
    ids
}

fn apply_deadlines(
    s: &mut State,
    ids: &Vec<String>,
    now: u64,
    cfg: &Config,
) -> (did: bool)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_deadlines(
            old(s)@,
            ids.deep_view(),
            now as nat,
        ),
        !did ==> final(s)@ == old(s)@,
        object_ids(*final(s)) == object_ids(*old(s)),
{
    let ghost a = s@;
    let ghost row_order = object_ids(*s);
    proof { lemma_reach_refl(now as nat, a); }
    let mut did = false;
    let mut i: usize = 0;
    while i < ids.len()
        invariant
            i <= ids@.len(),
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, a, s@),
            object_ids(*s) == row_order,
            now <= MAX_TIME,
            cfg.wf(),
            !did ==> s@ == a,
            s@ == executable_deadlines(
                a,
                ids.deep_view().take(i as int),
                now as nat,
            ),
        decreases ids@.len() - i,
    {
        let id = &ids[i];
        let due = match s.find_object(id) {
            Some(j) => {
                proof { s.lemma_object_at(j as int); }
                let pending = match s.objects[j].state {
                    PromiseState::Pending => true,
                    _ => false,
                };
                pending && s.objects[j].timeout_at <= now
            }
            None => false,
        };
        let ghost before = s@;
        s.process_promise_timeout(
            &PromiseTimeoutReq { id: clone_string(id) },
            now,
            cfg,
        );
        proof {
            lemma_reach_step(now as nat, a, before, s@);
            if !due {
                lemma_pass_deadline_noop(
                    before,
                    id@,
                    now as nat,
                );
                assert(s@ == before);
            }
            let prefix = ids.deep_view().take(i as int);
            assert(ids.deep_view().take(i as int + 1)
                =~= prefix.push(ids@[i as int]@));
            lemma_executable_deadlines_push(
                a,
                prefix,
                ids@[i as int]@,
                now as nat,
            );
        }
        if due {
            did = true;
        }
        i += 1;
    }
    assert(ids.deep_view().take(ids@.len() as int) =~= ids.deep_view());
    did
}

fn apply_leases(
    s: &mut State,
    ids: &Vec<String>,
    now: u64,
    cfg: &Config,
) -> (did: bool)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_leases(
            old(s)@,
            ids.deep_view(),
            now as nat,
        ),
        !did ==> final(s)@ == old(s)@,
        object_ids(*final(s)) == object_ids(*old(s)),
{
    let ghost a = s@;
    let ghost row_order = object_ids(*s);
    proof { lemma_reach_refl(now as nat, a); }
    let mut did = false;
    let mut i: usize = 0;
    while i < ids.len()
        invariant
            i <= ids@.len(),
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, a, s@),
            object_ids(*s) == row_order,
            now <= MAX_TIME,
            cfg.wf(),
            !did ==> s@ == a,
            s@ == executable_leases(
                a,
                ids.deep_view().take(i as int),
                now as nat,
            ),
        decreases ids@.len() - i,
    {
        let id = &ids[i];
        let due = match s.find_object(id) {
            Some(j) => {
                proof { s.lemma_object_at(j as int); }
                let p = &s.objects[j];
                let pending = match p.state {
                    PromiseState::Pending => true,
                    _ => false,
                };
                match &p.task {
                    Some(t) => match t.lease_timeout_at {
                        Some(at) => {
                            let acquired = match t.state {
                                TaskState::Acquired => true,
                                _ => false,
                            };
                            acquired && at <= now && pending && p.timeout_at > now
                        }
                        None => false,
                    },
                    None => false,
                }
            }
            None => false,
        };
        let ghost before = s@;
        s.process_lease_timeout(
            &TaskLeaseTimeoutReq { id: clone_string(id) },
            now,
            cfg,
        );
        proof {
            lemma_reach_step(now as nat, a, before, s@);
            reveal(lease_due);
            if !due {
                assert(!before.objects.contains_key(id@)
                    || !lease_due(before.objects[id@], now as nat));
                assert(s@ == before);
            }
            let prefix = ids.deep_view().take(i as int);
            assert(ids.deep_view().take(i as int + 1)
                =~= prefix.push(ids@[i as int]@));
            lemma_executable_leases_push(
                a,
                prefix,
                ids@[i as int]@,
                now as nat,
            );
        }
        if due {
            did = true;
        }
        i += 1;
    }
    assert(ids.deep_view().take(ids@.len() as int) =~= ids.deep_view());
    did
}

/// Snapshot the settled rows still carrying callbacks or listeners, in
/// executable row order.
fn snapshot_owed(s: &State) -> (r: Vec<Owed>)
    requires s.wf(),
    ensures
        r.deep_view() == executable_owed_snapshot(s@, object_ids(*s)),
{
    let mut r: Vec<Owed> = Vec::new();
    let mut i: usize = 0;
    while i < s.objects.len()
        invariant
            i <= s.objects@.len(),
            s.wf(),
            r.deep_view() == executable_owed_snapshot(
                s@,
                object_ids(*s).take(i as int),
            ),
        decreases s.objects@.len() - i,
    {
        proof { s.lemma_object_at(i as int); }
        let p = &s.objects[i];
        let pending = match p.state { PromiseState::Pending => true, _ => false };
        if !pending && (p.callbacks.len() > 0 || p.listeners.len() > 0) {
            r.push(Owed {
                awaited: clone_string(&p.id),
                callbacks: clone_strings(&p.callbacks),
                listeners: clone_strings(&p.listeners),
            });
        }
        proof {
            let prefix = object_ids(*s).take(i as int);
            assert(object_ids(*s).take(i as int + 1)
                =~= prefix.push(s.objects@[i as int].id@));
            assert(object_ids(*s).take(i as int + 1)
                == prefix.push(s.objects@[i as int].id@));
            lemma_executable_owed_snapshot_push(
                s@,
                prefix,
                s.objects@[i as int].id@,
            );
        }
        i += 1;
    }
    assert(object_ids(*s).take(s.objects@.len() as int) =~= object_ids(*s));
    r
}

/// Apply every callback batch before any listener batch.
fn apply_callbacks_owed(s: &mut State, owed: &Vec<Owed>, now: u64, cfg: &Config)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_owed_callbacks(
            old(s)@,
            owed.deep_view(),
            now as nat,
        ),
        object_ids(*final(s)) == object_ids(*old(s)),
{
    let ghost a = s@;
    let ghost row_order = object_ids(*s);
    proof { lemma_reach_refl(now as nat, a); }
    let mut o: usize = 0;
    while o < owed.len()
        invariant
            o <= owed@.len(),
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, a, s@),
            object_ids(*s) == row_order,
            now <= MAX_TIME,
            cfg.wf(),
            s@ == executable_owed_callbacks(
                a,
                owed.deep_view().take(o as int),
                now as nat,
            ),
        decreases owed@.len() - o,
    {
        let ghost b = s@;
        let mut c: usize = 0;
        while c < owed[o].callbacks.len()
            invariant
                o < owed@.len(),
                c <= owed@[o as int].callbacks@.len(),
                s.wf(),
                inv(now as nat, s@),
                reach(now as nat, a, s@),
                object_ids(*s) == row_order,
                now <= MAX_TIME,
                cfg.wf(),
                s@ == executable_callbacks(
                    b,
                    owed@[o as int]@.awaited,
                    owed@[o as int]@.callbacks.take(c as int),
                    now as nat,
                ),
            decreases owed@[o as int].callbacks@.len() - c,
        {
            let ghost before = s@;
            let req = PromiseRegisterCallbackReq {
                awaited: clone_string(&owed[o].awaited),
                awaiter: clone_string(&owed[o].callbacks[c]),
            };
            s.process_callback(&req, now, cfg);
            proof {
                lemma_reach_step(now as nat, a, before, s@);
                let prefix = owed@[o as int]@.callbacks.take(c as int);
                assert(owed@[o as int]@.callbacks.take(c as int + 1)
                    =~= prefix.push(owed@[o as int]@.callbacks[c as int]));
                lemma_executable_callbacks_push(
                    b,
                    owed@[o as int]@.awaited,
                    prefix,
                    owed@[o as int]@.callbacks[c as int],
                    now as nat,
                );
            }
            c += 1;
        }
        proof {
            assert(owed@[o as int]@.callbacks.take(
                owed@[o as int]@.callbacks.len() as int,
            ) =~= owed@[o as int]@.callbacks);
            let prefix = owed.deep_view().take(o as int);
            assert(owed.deep_view().take(o as int + 1)
                =~= prefix.push(owed@[o as int]@));
            lemma_executable_owed_callbacks_push(
                a,
                prefix,
                owed@[o as int]@,
                now as nat,
            );
        }
        o += 1;
    }
    assert(owed.deep_view().take(owed@.len() as int) =~= owed.deep_view());
}

fn apply_listeners_owed(s: &mut State, owed: &Vec<Owed>, now: u64, cfg: &Config)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_owed_listeners(
            old(s)@,
            owed.deep_view(),
            now as nat,
        ),
        object_ids(*final(s)) == object_ids(*old(s)),
{
    let ghost a = s@;
    let ghost row_order = object_ids(*s);
    proof { lemma_reach_refl(now as nat, a); }
    let mut o: usize = 0;
    while o < owed.len()
        invariant
            o <= owed@.len(),
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, a, s@),
            object_ids(*s) == row_order,
            now <= MAX_TIME,
            cfg.wf(),
            s@ == executable_owed_listeners(
                a,
                owed.deep_view().take(o as int),
                now as nat,
            ),
        decreases owed@.len() - o,
    {
        let ghost b = s@;
        let mut l: usize = 0;
        while l < owed[o].listeners.len()
            invariant
                o < owed@.len(),
                l <= owed@[o as int].listeners@.len(),
                s.wf(),
                inv(now as nat, s@),
                reach(now as nat, a, s@),
                object_ids(*s) == row_order,
                now <= MAX_TIME,
                cfg.wf(),
                s@ == executable_listeners(
                    b,
                    owed@[o as int]@.awaited,
                    owed@[o as int]@.listeners.take(l as int),
                    now as nat,
                ),
            decreases owed@[o as int].listeners@.len() - l,
        {
            let ghost before = s@;
            let req = PromiseRegisterListenerReq {
                awaited: clone_string(&owed[o].awaited),
                address: clone_string(&owed[o].listeners[l]),
            };
            s.process_listener(&req, now, cfg);
            proof {
                lemma_reach_step(now as nat, a, before, s@);
                let prefix = owed@[o as int]@.listeners.take(l as int);
                assert(owed@[o as int]@.listeners.take(l as int + 1)
                    =~= prefix.push(owed@[o as int]@.listeners[l as int]));
                lemma_executable_listeners_push(
                    b,
                    owed@[o as int]@.awaited,
                    prefix,
                    owed@[o as int]@.listeners[l as int],
                    now as nat,
                );
            }
            l += 1;
        }
        proof {
            assert(owed@[o as int]@.listeners.take(
                owed@[o as int]@.listeners.len() as int,
            ) =~= owed@[o as int]@.listeners);
            let prefix = owed.deep_view().take(o as int);
            assert(owed.deep_view().take(o as int + 1)
                =~= prefix.push(owed@[o as int]@));
            lemma_executable_owed_listeners_push(
                a,
                prefix,
                owed@[o as int]@,
                now as nat,
            );
        }
        o += 1;
    }
    assert(owed.deep_view().take(owed@.len() as int) =~= owed.deep_view());
}

fn apply_owed(s: &mut State, owed: &Vec<Owed>, now: u64, cfg: &Config)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_owed(old(s)@, owed.deep_view(), now as nat),
        final(s)@.schedules == old(s)@.schedules,
        final(s)@.objects.dom() == old(s)@.objects.dom(),
        object_ids(*final(s)) == object_ids(*old(s)),
{
    let ghost a = s@;
    apply_callbacks_owed(s, owed, now, cfg);
    let ghost after_callbacks = s@;
    apply_listeners_owed(s, owed, now, cfg);
    proof {
        lemma_reach_trans(now as nat, a, after_callbacks, s@);
        lemma_executable_owed_frame(a, owed.deep_view(), now as nat);
    }
}

/// Snapshot retry ids after the owed pass, in executable row order.
fn snapshot_due(s: &State, now: u64) -> (r: Vec<String>)
    requires s.wf(),
    ensures
        r.deep_view() == executable_due_snapshot(
            s@,
            object_ids(*s),
            now as nat,
        ),
{
    let mut r: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < s.objects.len()
        invariant
            i <= s.objects@.len(),
            s.wf(),
            r.deep_view() == executable_due_snapshot(
                s@,
                object_ids(*s).take(i as int),
                now as nat,
            ),
        decreases s.objects@.len() - i,
    {
        proof { s.lemma_object_at(i as int); }
        let p = &s.objects[i];
        let pending = match p.state { PromiseState::Pending => true, _ => false };
        let task_due = match &p.task {
            Some(t) => match t.retry_timeout_at {
                Some(d) => {
                    let task_pending = match t.state { TaskState::Pending => true, _ => false };
                    task_pending && d <= now
                }
                None => false,
            },
            None => false,
        };
        if pending && task_due && p.timeout_at > now {
            r.push(clone_string(&p.id));
        }
        proof {
            let prefix = object_ids(*s).take(i as int);
            assert(object_ids(*s).take(i as int + 1)
                =~= prefix.push(s.objects@[i as int].id@));
            assert(object_ids(*s).take(i as int + 1)
                == prefix.push(s.objects@[i as int].id@));
            lemma_executable_due_snapshot_push(
                s@,
                prefix,
                s.objects@[i as int].id@,
                now as nat,
            );
            reveal(retry_due);
        }
        i += 1;
    }
    assert(object_ids(*s).take(s.objects@.len() as int) =~= object_ids(*s));
    r
}

/// Apply a snapshotted retry list exactly.
fn apply_due(s: &mut State, due: &Vec<String>, now: u64, cfg: &Config)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_due(
            old(s)@,
            due.deep_view(),
            now as nat,
            cfg.retry_timeout as nat,
        ),
        final(s)@.schedules == old(s)@.schedules,
        final(s)@.objects.dom() == old(s)@.objects.dom(),
        object_ids(*final(s)) == object_ids(*old(s)),
{
    let ghost a = s@;
    let ghost row_order = object_ids(*s);
    proof { lemma_reach_refl(now as nat, a); }
    let mut d: usize = 0;
    while d < due.len()
        invariant
            d <= due@.len(),
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, a, s@),
            object_ids(*s) == row_order,
            now <= MAX_TIME,
            cfg.wf(),
            s@ == executable_due(
                a,
                due.deep_view().take(d as int),
                now as nat,
                cfg.retry_timeout as nat,
            ),
        decreases due@.len() - d,
    {
        let ghost before = s@;
        s.process_retry_timeout(
            &TaskRetryTimeoutReq { id: clone_string(&due[d]) },
            now,
            cfg,
        );
        proof {
            lemma_reach_step(now as nat, a, before, s@);
            let prefix = due.deep_view().take(d as int);
            assert(due.deep_view().take(d as int + 1)
                =~= prefix.push(due@[d as int]@));
            lemma_executable_due_push(
                a,
                prefix,
                due@[d as int]@,
                now as nat,
                cfg.retry_timeout as nat,
            );
        }
        d += 1;
    }
    assert(due.deep_view().take(due@.len() as int) =~= due.deep_view());
    proof {
        lemma_executable_due_frame(
            a,
            due.deep_view(),
            now as nat,
            cfg.retry_timeout as nat,
        );
    }
}

} // verus!
