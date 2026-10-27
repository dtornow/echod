//! The steps a node runs around a request, verified: the instant a step is
//! decided at, the sweep that fires what is due, the drain that discharges
//! what a step left owed, and the nearest deadline a document owes a timer
//! for.
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

/// What `drain` ensures: kernel steps at `now` that leave the schedules and
/// every object's key as they were. The system model's relation for the
/// steps after a handler or a fire.
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

/// One iteration of `sweep`'s object loop: projection, lease reclamation,
/// then retry dispatch.  The outbox update is included.
pub open spec fn executable_sweep_one(
    a: AState,
    id: Seq<char>,
    now: nat,
    retry_timeout: nat,
) -> AState {
    let a1 = with_objects(a, promise_timeout_objects(a, id, now));
    let a2 = with_objects(a1, lease_timeout_objects(a1, id, now));
    retry_timeout_state(a2, id, now, retry_timeout)
}

/// The exact phase and row order of `sweep`: all three operations on a row
/// before moving to the next row.
pub open spec fn executable_sweep_rows(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        executable_sweep_one(
            executable_sweep_rows(a, ids.drop_last(), now, retry_timeout),
            ids.last(),
            now,
            retry_timeout,
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

/// The settled rows and their callback/listener lists, snapshotted at the
/// start of one drain round in stored row order.
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

/// Process an owed snapshot in order. Each row's callback list is processed
/// before its listener list, exactly as the executable loop does.
pub open spec fn executable_owed(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
) -> AState
    decreases owed.len(),
{
    if owed.len() == 0 {
        a
    } else {
        let a1 = executable_owed(a, owed.drop_last(), now);
        let item = owed.last();
        let a2 = executable_callbacks(a1, item.awaited, item.callbacks, now);
        executable_listeners(a2, item.awaited, item.listeners, now)
    }
}

/// Retry ids snapshotted after owed callbacks and listeners have run.
pub open spec fn executable_retry_selected(p: APromise, now: nat) -> bool {
    &&& p.state == PromiseState::Pending
    &&& p.task is Some
    &&& p.task.unwrap().state == TaskState::Pending
    &&& p.task.unwrap().retry_timeout_at is Some
    &&& p.task.unwrap().retry_timeout_at.unwrap() <= now
}

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
        if a.objects.contains_key(x)
            && executable_retry_selected(a.objects[x], now)
        {
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

pub open spec fn executable_drain_round(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
) -> AState {
    let owed = executable_owed_snapshot(a, ids);
    let after_owed = executable_owed(a, owed, now);
    let due = executable_due_snapshot(after_owed, ids, now);
    executable_due(after_owed, due, now, retry_timeout)
}

pub open spec fn executable_round_has_work(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
) -> bool {
    let owed = executable_owed_snapshot(a, ids);
    let after_owed = executable_owed(a, owed, now);
    owed.len() > 0 || executable_due_snapshot(after_owed, ids, now).len() > 0
}

/// The executable drain's bounded loop, including its early return.  The
/// production loop executes at most 65 rounds.
pub open spec fn executable_drain_rows(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
    fuel: nat,
) -> AState
    decreases fuel,
{
    if fuel == 0 || !executable_round_has_work(a, ids, now) {
        a
    } else {
        executable_drain_rows(
            executable_drain_round(a, ids, now, retry_timeout),
            ids,
            now,
            retry_timeout,
            (fuel - 1) as nat,
        )
    }
}

/// What `logic::flight::decide` does for an internal sweep, at map level.
/// The order argument comes from `State::objects`, not from the map.
pub open spec fn executable_sweep_and_drain(
    a: AState,
    ids: Seq<Seq<char>>,
    now: nat,
    retry_timeout: nat,
) -> AState {
    let swept = executable_sweep_rows(a, ids, now, retry_timeout);
    executable_drain_rows(swept, ids, now, retry_timeout, 65)
}

proof fn lemma_executable_sweep_rows_push(
    a: AState,
    ids: Seq<Seq<char>>,
    id: Seq<char>,
    now: nat,
    retry_timeout: nat,
)
    ensures
        executable_sweep_rows(a, ids.push(id), now, retry_timeout)
            == executable_sweep_one(
                executable_sweep_rows(a, ids, now, retry_timeout),
                id,
                now,
                retry_timeout,
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

proof fn lemma_executable_owed_push(
    a: AState,
    owed: Seq<AOwed>,
    item: AOwed,
    now: nat,
)
    ensures
        executable_owed(a, owed.push(item), now)
            == executable_listeners(
                executable_callbacks(
                    executable_owed(a, owed, now),
                    item.awaited,
                    item.callbacks,
                    now,
                ),
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
            == if a.objects.contains_key(id)
                && executable_retry_selected(a.objects[id], now)
            {
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

proof fn lemma_executable_owed_frame(
    a: AState,
    owed: Seq<AOwed>,
    now: nat,
)
    ensures
        executable_owed(a, owed, now).schedules == a.schedules,
        executable_owed(a, owed, now).objects.dom() == a.objects.dom(),
    decreases owed.len(),
{
    if owed.len() > 0 {
        lemma_executable_owed_frame(a, owed.drop_last(), now);
        let b = executable_owed(a, owed.drop_last(), now);
        let item = owed.last();
        lemma_executable_callbacks_frame(
            b,
            item.awaited,
            item.callbacks,
            now,
        );
        let c = executable_callbacks(
            b,
            item.awaited,
            item.callbacks,
            now,
        );
        lemma_executable_listeners_frame(
            c,
            item.awaited,
            item.listeners,
            now,
        );
    }
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

/// What one object looks like after the three sweeper steps at `now`,
/// given the catalogue: nothing in it is due.
proof fn lemma_swept_object(now: nat, s0: AState, s1: AState, s2: AState, s3: AState, id: Seq<char>, rt: nat)
    requires
        inv(now, s0), inv(now, s1), inv(now, s2), inv(now, s3),
        s1.objects == promise_timeout_objects(s0, id, now),
        s2.objects == lease_timeout_objects(s1, id, now),
        s3.objects == retry_timeout_objects(s2, id, now, rt),
        0 < rt <= MAX_TIME, now <= MAX_TIME,
    ensures
        s3.objects.contains_key(id) ==> cleared(s3.objects[id], now),
        forall |x: Seq<char>| x != id ==> (s3.objects.contains_key(x) <==> s0.objects.contains_key(x)) && (s0.objects.contains_key(x) ==> s3.objects[x] == s0.objects[x]),
        s3.objects.dom() == s0.objects.dom(),
{
    reveal(inv);
    if s0.objects.contains_key(id) {
        let p0 = s0.objects[id];
        let p1 = s1.objects[id];
        let p2 = s2.objects[id];
        let p3 = s3.objects[id];
        assert(p1 == p0.project(now));
        // after projection: pending means the deadline is ahead; settled means the task is fulfilled and cleared
        assert(p1.state == PromiseState::Pending ==> p1.timeout_at > now);
        assert(p2.state == p1.state && p2.timeout_at == p1.timeout_at);
        assert(p3.state == p1.state && p3.timeout_at == p1.timeout_at);
        assert forall |t: nat| deadline_at(p3, t) implies t > now by {
            if promise_deadline(p3) == Some(t) {
                assert(t == p3.timeout_at as nat);
                assert(t > now);
            } else if lease_deadline(p3) == Some(t) {
                let t3 = p3.task.unwrap();
                assert(t3.lease_timeout_at is Some && t == t3.lease_timeout_at.unwrap() as nat);
                assert(t3.state == TaskState::Acquired);
                if p1.state != PromiseState::Pending {
                    assert(false);
                } else {
                    assert(!lease_due(p1, now));
                    assert(p2 == p1);
                    assert(!retry_due(p2, now) || p3.task.unwrap().lease_timeout_at == p2.task.unwrap().lease_timeout_at);
                    assert(t > now);
                }
            } else {
                let t3 = p3.task.unwrap();
                assert(t3.retry_timeout_at is Some && t == t3.retry_timeout_at.unwrap() as nat);
                assert(t3.state == TaskState::Pending);
                if p1.state != PromiseState::Pending {
                    assert(false);
                } else {
                    if retry_due(p2, now) {
                        // re-offered: the next offer on the task's grid, after `now`
                        // and at most `rt` ahead, and the sum fits
                        let t2 = p2.task.unwrap();
                        assert(t3 == t2.rearm(now, rt));
                        let due = crate::properties::opt_or_zero(t2.retry_timeout_at);
                        crate::object::lemma_next_offer(due, now, rt);
                        assert(now + rt <= 2 * (MAX_TIME as nat));
                        assert(t3.retry_timeout_at == Some(crate::object::next_offer(due, now, rt) as u64));
                        assert(t == crate::object::next_offer(due, now, rt));
                    } else {
                        if lease_due(p1, now) {
                            // reclaimed: its first offer is due at the lease's end, already passed
                            let end = p1.task.unwrap().lease_timeout_at.unwrap();
                            assert(p2.task.unwrap().retry_timeout_at == Some(end));
                            assert(retry_due(p2, now));
                            assert(false);
                        }
                    }
                    assert(t > now);
                }
            }
        }
    }
    assert(s3.objects.dom() =~= s0.objects.dom());
}

/// Fire what is due in a document at `now`: deadlines, leases, retries, one
/// object at a time. Returns whether anything fired. After it, nothing in
/// the document is due at `now`; if nothing fired, the document is as it was.
pub fn sweep(s: &mut State, now: u64, cfg: &Config) -> (did: bool)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        swept_by(now as nat, old(s)@, final(s)@, did),
        object_ids(*final(s)) == object_ids(*old(s)),
        final(s)@ == executable_sweep_rows(
            old(s)@,
            object_ids(*old(s)),
            now as nat,
            cfg.retry_timeout as nat,
        ),
{
    let ghost a = s@;
    let ghost row_order = object_ids(*s);
    proof { lemma_reach_refl(now as nat, a); }
    let mut ids: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < s.objects.len()
        invariant
            i <= s.objects@.len(),
            ids@.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] ids@[j]@ == s.objects@[j].id@,
        decreases s.objects@.len() - i,
    {
        ids.push(clone_string(&s.objects[i].id));
        i += 1;
    }
    proof {
        lemma_fold_dom(s.objects@, obj_key(), obj_val());
        assert(ids.deep_view() =~= row_order);
        assert forall |id: Seq<char>| #[trigger] a.objects.contains_key(id) implies exists |j: int| 0 <= j < ids@.len() && #[trigger] ids@[j]@ == id by {
            assert(mentions(s.objects@, obj_key(), id));
            let j = choose |j: int| 0 <= j < s.objects@.len() && #[trigger] obj_key()(s.objects@[j]) == id;
            assert(ids@[j]@ == id);
        }
    }
    let mut did = false;
    let mut k: usize = 0;
    while k < ids.len()
        invariant
            k <= ids@.len(),
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, a, s@),
            s@.schedules == a.schedules,
            s@.objects.dom() == a.objects.dom(),
            now <= MAX_TIME,
            cfg.wf(),
            forall |j: int| 0 <= j < k && s@.objects.contains_key(#[trigger] ids@[j]@) ==> cleared(s@.objects[ids@[j]@], now as nat),
            !did ==> s@ == a,
            ids.deep_view() == row_order,
            object_ids(*s) == row_order,
            s@ == executable_sweep_rows(
                a,
                ids.deep_view().take(k as int),
                now as nat,
                cfg.retry_timeout as nat,
            ),
            forall |id: Seq<char>| #[trigger] a.objects.contains_key(id) ==> exists |j: int| 0 <= j < ids@.len() && #[trigger] ids@[j]@ == id,
        decreases ids@.len() - k,
    {
        let id = &ids[k];
        let ghost s0 = s@;
        let due_p = match s.find_object(id) {
            Some(i) => {
                proof { s.lemma_object_at(i as int); }
                let pending = match s.objects[i].state { PromiseState::Pending => true, _ => false };
                pending && s.objects[i].timeout_at <= now
            }
            None => false,
        };
        s.process_promise_timeout(&PromiseTimeoutReq { id: clone_string(id) }, now, cfg);
        let ghost s1 = s@;
        proof { lemma_reach_step(now as nat, a, s0, s1); }
        let due_l = match s.find_object(id) {
            Some(i) => {
                proof { s.lemma_object_at(i as int); }
                let p = &s.objects[i];
                let pending = match p.state { PromiseState::Pending => true, _ => false };
                match &p.task {
                    Some(t) => match t.lease_timeout_at {
                        Some(d) => {
                            let acquired = match t.state { TaskState::Acquired => true, _ => false };
                            acquired && d <= now && pending && p.timeout_at > now
                        }
                        None => false,
                    },
                    None => false,
                }
            }
            None => false,
        };
        s.process_lease_timeout(&TaskLeaseTimeoutReq { id: clone_string(id) }, now, cfg);
        let ghost s2 = s@;
        proof { lemma_reach_step(now as nat, a, s1, s2); }
        let due_r = match s.find_object(id) {
            Some(i) => {
                proof { s.lemma_object_at(i as int); }
                let p = &s.objects[i];
                let pending = match p.state { PromiseState::Pending => true, _ => false };
                match &p.task {
                    Some(t) => match t.retry_timeout_at {
                        Some(d) => {
                            let tpending = match t.state { TaskState::Pending => true, _ => false };
                            tpending && d <= now && pending && p.timeout_at > now
                        }
                        None => false,
                    },
                    None => false,
                }
            }
            None => false,
        };
        s.process_retry_timeout(&TaskRetryTimeoutReq { id: clone_string(id) }, now, cfg);
        let ghost s3 = s@;
        proof { lemma_reach_step(now as nat, a, s2, s3); }
        if due_p || due_l || due_r {
            did = true;
        }
        proof {
            let x = id@;
            assert(s1 == with_objects(s0, promise_timeout_objects(s0, x, now as nat)));
            assert(s2 == with_objects(s1, lease_timeout_objects(s1, x, now as nat)));
            assert(s3 == retry_timeout_state(s2, x, now as nat, cfg.retry_timeout as nat));
            assert(ids.deep_view().take(k as int + 1)
                =~= ids.deep_view().take(k as int).push(x));
            let prefix = ids.deep_view().take(k as int);
            assert(ids.deep_view().take(k as int + 1) == prefix.push(x));
            assert(s0 == executable_sweep_rows(
                a,
                prefix,
                now as nat,
                cfg.retry_timeout as nat,
            ));
            assert(executable_sweep_one(
                s0,
                x,
                now as nat,
                cfg.retry_timeout as nat,
            ) == s3);
            lemma_executable_sweep_rows_push(
                a,
                prefix,
                x,
                now as nat,
                cfg.retry_timeout as nat,
            );
            assert(executable_sweep_rows(
                a,
                ids.deep_view().take(k as int + 1),
                now as nat,
                cfg.retry_timeout as nat,
            ) == s3);
            lemma_swept_object(now as nat, s0, s1, s2, s3, x, cfg.retry_timeout as nat);
            assert(s3.objects.dom() =~= a.objects.dom());
            if !(due_p || due_l || due_r) {
                // nothing fired: each step left the object as it was
                reveal(inv);
                if s0.objects.contains_key(x) {
                    let p0 = s0.objects[x];
                    assert(p0.project(now as nat) == p0);
                    assert(s1.objects =~= s0.objects);
                    assert(!lease_due(p0, now as nat));
                    assert(s2.objects =~= s0.objects);
                    assert(!retry_due(p0, now as nat));
                    assert(s3.objects =~= s0.objects);
                } else {
                    assert(s3.objects =~= s0.objects);
                }
                assert(s3 == s0);
            }
        }
        k += 1;
    }
    proof {
        assert(ids.deep_view().take(ids.len() as int) =~= row_order);
        assert forall |id: Seq<char>| #[trigger] s@.objects.contains_key(id) implies cleared(s@.objects[id], now as nat) by {
            let j = choose |j: int| 0 <= j < ids@.len() && #[trigger] ids@[j]@ == id;
        }
    }
    did
}

// ---------------------------------------------------------------------------
// The drain
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

/// Apply an owed snapshot exactly as the executable nested loops do.
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
            s@ == executable_owed(
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
        }
        let ghost after_callbacks = s@;
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
                    after_callbacks,
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
                    after_callbacks,
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
            lemma_executable_owed_push(
                a,
                prefix,
                owed@[o as int]@,
                now as nat,
            );
        }
        o += 1;
    }
    assert(owed.deep_view().take(owed@.len() as int) =~= owed.deep_view());
    proof {
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
        if pending && task_due {
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
            reveal(executable_retry_selected);
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

/// One exact drain round, including both snapshots.
fn drain_round(s: &mut State, now: u64, cfg: &Config) -> (did: bool)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_drain_round(
            old(s)@,
            object_ids(*old(s)),
            now as nat,
            cfg.retry_timeout as nat,
        ),
        did == executable_round_has_work(
            old(s)@,
            object_ids(*old(s)),
            now as nat,
        ),
        final(s)@.schedules == old(s)@.schedules,
        final(s)@.objects.dom() == old(s)@.objects.dom(),
        object_ids(*final(s)) == object_ids(*old(s)),
{
    let ghost a = s@;
    let ghost ids = object_ids(*s);
    let owed = snapshot_owed(s);
    apply_owed(s, &owed, now, cfg);
    let ghost after_owed = s@;
    let due = snapshot_due(s, now);
    apply_due(s, &due, now, cfg);
    proof {
        lemma_reach_trans(now as nat, a, after_owed, s@);
        assert(owed.deep_view() == executable_owed_snapshot(a, ids));
        assert(object_ids(*s) == ids);
    }
    !owed.is_empty() || !due.is_empty()
}

fn drain_fuel(s: &mut State, now: u64, cfg: &Config, fuel: u64)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        drained(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_drain_rows(
            old(s)@,
            object_ids(*old(s)),
            now as nat,
            cfg.retry_timeout as nat,
            fuel as nat,
        ),
        final(s)@.schedules == old(s)@.schedules,
        final(s)@.objects.dom() == old(s)@.objects.dom(),
        object_ids(*final(s)) == object_ids(*old(s)),
    decreases fuel,
{
    let ghost a = s@;
    let ghost ids = object_ids(*s);
    if fuel == 0 {
        proof { lemma_reach_refl(now as nat, a); }
        return;
    }
    let did = drain_round(s, now, cfg);
    let ghost b = s@;
    if !did {
        proof {
            assert(!executable_round_has_work(a, ids, now as nat));
            assert(b == executable_drain_round(
                a,
                ids,
                now as nat,
                cfg.retry_timeout as nat,
            ));
            assert(b == a);
        }
        return;
    }
    drain_fuel(s, now, cfg, fuel - 1);
    proof {
        lemma_reach_trans(now as nat, a, b, s@);
        assert(object_ids(*s) == ids);
    }
}

/// Discharge every settled promise's callbacks and listeners, then fire
/// every retry that is due, until nothing is owed or 65 rounds have run.
/// The exact bounded transition is `executable_drain_rows`.
pub fn drain(s: &mut State, now: u64, cfg: &Config)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        drained(now as nat, old(s)@, final(s)@),
        final(s)@ == executable_drain_rows(
            old(s)@,
            object_ids(*old(s)),
            now as nat,
            cfg.retry_timeout as nat,
            65,
        ),
        object_ids(*final(s)) == object_ids(*old(s)),
{
    drain_fuel(s, now, cfg, 65);
}

} // verus!
