//! The steps a node runs around a request, verified: the instant a step is
//! decided at, the sweep that fires what is due, the drain that discharges
//! what a step left owed, and the nearest deadline a document owes a timer
//! for.
//!
//! The kernel proves each handler and each internal step against the
//! catalogue; this module composes them. What it adds, and the fleet model
//! relies on: after a sweep at `now` nothing in the document is due at `now`
//! (`no_due`), a sweep that fired nothing left the document as it was, and
//! `next_deadline` is the least deadline of the document (`is_next`).

use vstd::prelude::*;

use echod_kernel::external::pre;
use echod_kernel::internal::*;
use echod_kernel::properties::*;
use echod_kernel::store::{distinct_by, fold_by, lemma_fold_distinct, lemma_fold_dom, mentions, obj_key, obj_val, AState, State};
use echod_kernel::tags::OType;
use echod_kernel::types::*;

verus! {

/// An origin's document: its objects, as the kernel sees them.
pub type Doc = Map<Seq<char>, APromise>;

/// A document as a kernel state: the objects alone, no schedule, nothing
/// in the outbox.
pub open spec fn full(d: Doc) -> AState {
    AState { objects: d, schedules: Map::empty(), outbox: Map::empty() }
}

// ---------------------------------------------------------------------------
// Deadlines
// ---------------------------------------------------------------------------

/// A pending promise that is not internal owes a timer at its deadline.
pub open spec fn promise_deadline(p: APromise) -> Option<nat> {
    if p.state == PromiseState::Pending && p.otype() != OType::Internal { Some(p.timeout_at) } else { None }
}

pub open spec fn lease_deadline(p: APromise) -> Option<nat> {
    match p.task { Some(t) => t.lease_timeout_at, None => None }
}

pub open spec fn retry_deadline(p: APromise) -> Option<nat> {
    match p.task { Some(t) => t.retry_timeout_at, None => None }
}

pub open spec fn deadline_at(p: APromise, t: nat) -> bool {
    promise_deadline(p) == Some(t) || lease_deadline(p) == Some(t) || retry_deadline(p) == Some(t)
}

pub open spec fn has_deadline(d: Doc, t: nat) -> bool {
    exists |id: Seq<char>| #[trigger] d.contains_key(id) && deadline_at(d[id], t)
}

/// `t` is the least deadline of the document.
pub open spec fn is_next(d: Doc, t: nat) -> bool {
    has_deadline(d, t) && forall |u: nat| has_deadline(d, u) ==> t <= u
}

/// Nothing in the object is due at `now`.
pub open spec fn cleared(p: APromise, now: nat) -> bool {
    forall |t: nat| deadline_at(p, t) ==> t > now
}

pub open spec fn no_due(now: nat, d: Doc) -> bool {
    forall |id: Seq<char>| #[trigger] d.contains_key(id) ==> cleared(d[id], now)
}

pub proof fn lemma_no_due(now: nat, d: Doc)
    requires no_due(now, d),
    ensures forall |t: nat| has_deadline(d, t) ==> t > now,
{
    assert forall |t: nat| has_deadline(d, t) implies t > now by {
        let id = choose |id: Seq<char>| #[trigger] d.contains_key(id) && deadline_at(d[id], t);
        assert(cleared(d[id], now));
    }
}

// ---------------------------------------------------------------------------
// Kernel steps, chained
// ---------------------------------------------------------------------------

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
    ensures inv(now, full(s.objects)),
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

/// The least deadline of the rows, which fold to the document.
pub fn next_deadline(rows: &Vec<Promise>) -> (r: Option<u64>)
    requires distinct_by(rows@, obj_key()),
    ensures
        match r {
            Some(d) => is_next(fold_by(rows@, obj_key(), obj_val()), d as nat),
            None => forall |t: nat| !has_deadline(fold_by(rows@, obj_key(), obj_val()), t),
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
        let internal = match echod_kernel::tags::exec_otype(&p.tags) { OType::Internal => true, _ => false };
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
            assert(promise_deadline(ap) == (if pending && !internal { Some(ap.timeout_at) } else { None }));
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
        assert forall |t: nat| has_deadline(d, t) implies exists |j: int| 0 <= j < rows@.len() && #[trigger] deadline_at(rows@[j]@, t) by {
            let id = choose |id: Seq<char>| #[trigger] d.contains_key(id) && deadline_at(d[id], t);
            assert(mentions(rows@, obj_key(), id));
            let j = choose |j: int| 0 <= j < rows@.len() && #[trigger] obj_key()(rows@[j]) == id;
            assert(d[obj_key()(rows@[j])] == obj_val()(rows@[j]));
            assert(deadline_at(rows@[j]@, t));
        }
        assert forall |j: int, t: nat| 0 <= j < rows@.len() && #[trigger] deadline_at(rows@[j]@, t) implies has_deadline(d, t) by {
            assert(d.contains_key(obj_key()(rows@[j])));
            assert(d[obj_key()(rows@[j])] == obj_val()(rows@[j]));
        }
    }
    min
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
        rt > 0,
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
            } else if lease_deadline(p3) == Some(t) {
                let t3 = p3.task.unwrap();
                assert(t3.state == TaskState::Acquired);
                if p1.state != PromiseState::Pending {
                    assert(false);
                } else {
                    assert(!lease_due(p1, now));
                    assert(p2 == p1);
                    assert(!retry_due(p2, now) || p3.task.unwrap().lease_timeout_at == p2.task.unwrap().lease_timeout_at);
                }
            } else {
                let t3 = p3.task.unwrap();
                assert(t3.state == TaskState::Pending);
                if p1.state != PromiseState::Pending {
                    assert(false);
                } else {
                    if retry_due(p2, now) {
                    } else {
                        if lease_due(p1, now) {
                            assert(p2.task.unwrap().retry_timeout_at == Some(now));
                            assert(retry_due(p2, now));
                            assert(false);
                        }
                    }
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
        reach(now as nat, old(s)@, final(s)@),
        final(s)@.schedules == old(s)@.schedules,
        final(s)@.objects.dom() == old(s)@.objects.dom(),
        no_due(now as nat, final(s)@.objects),
        !did ==> final(s)@ == old(s)@,
{
    let ghost a = s@;
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
        ids.push(echod_kernel::ident::clone_string(&s.objects[i].id));
        i += 1;
    }
    proof {
        lemma_fold_dom(s.objects@, obj_key(), obj_val());
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
        s.process_promise_timeout(&PromiseTimeoutReq { id: echod_kernel::ident::clone_string(id) }, now, cfg);
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
        s.process_lease_timeout(&TaskLeaseTimeoutReq { id: echod_kernel::ident::clone_string(id) }, now, cfg);
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
        s.process_retry_timeout(&TaskRetryTimeoutReq { id: echod_kernel::ident::clone_string(id) }, now, cfg);
        let ghost s3 = s@;
        proof { lemma_reach_step(now as nat, a, s2, s3); }
        if due_p || due_l || due_r {
            did = true;
        }
        proof {
            let x = id@;
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
struct Owed {
    awaited: String,
    callbacks: Vec<String>,
    listeners: Vec<String>,
}

fn clone_strings(v: &Vec<String>) -> (r: Vec<String>)
    ensures r.deep_view() == v.deep_view(),
{
    let mut r: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@.len() == i, forall |j: int| 0 <= j < i ==> #[trigger] r@[j]@ == v@[j]@,
        decreases v@.len() - i,
    {
        r.push(echod_kernel::ident::clone_string(&v[i]));
        i += 1;
    }
    assert(r.deep_view() =~= v.deep_view());
    r
}

/// Discharge every settled promise's callbacks and listeners, then fire
/// every retry that is due, until nothing is owed or the round limit is
/// reached. Every step is a kernel step at `now`.
pub fn drain(s: &mut State, now: u64, cfg: &Config)
    requires pre(*old(s), now, *cfg),
    ensures
        final(s).wf(),
        inv(now as nat, final(s)@),
        reach(now as nat, old(s)@, final(s)@),
        final(s)@.schedules == old(s)@.schedules,
{
    proof { lemma_reach_refl(now as nat, old(s)@); }
    let mut rounds: u64 = 0;
    while rounds <= 64
        invariant
            s.wf(),
            inv(now as nat, s@),
            reach(now as nat, old(s)@, s@),
            s@.schedules == old(s)@.schedules,
            now <= MAX_TIME,
            cfg.wf(),
        decreases 65 - rounds,
    {
        rounds += 1;
        let mut did = false;
        let mut owed: Vec<Owed> = Vec::new();
        let mut i: usize = 0;
        while i < s.objects.len()
            invariant i <= s.objects@.len(),
            decreases s.objects@.len() - i,
        {
            let p = &s.objects[i];
            let pending = match p.state { PromiseState::Pending => true, _ => false };
            if !pending && (p.callbacks.len() > 0 || p.listeners.len() > 0) {
                owed.push(Owed { awaited: echod_kernel::ident::clone_string(&p.id), callbacks: clone_strings(&p.callbacks), listeners: clone_strings(&p.listeners) });
            }
            i += 1;
        }
        let mut o: usize = 0;
        while o < owed.len()
            invariant
                o <= owed@.len(),
                s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, now <= MAX_TIME, cfg.wf(),
            decreases owed@.len() - o,
        {
            let mut c: usize = 0;
            while c < owed[o].callbacks.len()
                invariant
                    o < owed@.len(),
                    c <= owed@[o as int].callbacks@.len(),
                    s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, now <= MAX_TIME, cfg.wf(),
                decreases owed@[o as int].callbacks@.len() - c,
            {
                let ghost b = s@;
                let req = PromiseRegisterCallbackReq { awaited: echod_kernel::ident::clone_string(&owed[o].awaited), awaiter: echod_kernel::ident::clone_string(&owed[o].callbacks[c]) };
                s.process_callback(&req, now, cfg);
                proof {
                    assert(inv(now as nat, s@));
                    assert(legal(now as nat, b, s@));
                    assert(kstep(now as nat, b, s@));
                    lemma_reach_step(now as nat, old(s)@, b, s@);
                }
                did = true;
                c += 1;
            }
            let mut l: usize = 0;
            while l < owed[o].listeners.len()
                invariant
                    o < owed@.len(),
                    l <= owed@[o as int].listeners@.len(),
                    s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, now <= MAX_TIME, cfg.wf(),
                decreases owed@[o as int].listeners@.len() - l,
            {
                let ghost b = s@;
                let req = PromiseRegisterListenerReq { awaited: echod_kernel::ident::clone_string(&owed[o].awaited), address: echod_kernel::ident::clone_string(&owed[o].listeners[l]) };
                s.process_listener(&req, now, cfg);
                proof { lemma_reach_step(now as nat, old(s)@, b, s@); }
                did = true;
                l += 1;
            }
            o += 1;
        }
        let mut due: Vec<String> = Vec::new();
        let mut i: usize = 0;
        while i < s.objects.len()
            invariant i <= s.objects@.len(),
            decreases s.objects@.len() - i,
        {
            let p = &s.objects[i];
            let pending = match p.state { PromiseState::Pending => true, _ => false };
            let task_due = match &p.task {
                Some(t) => match t.retry_timeout_at {
                    Some(d) => { let tp = match t.state { TaskState::Pending => true, _ => false }; tp && d <= now }
                    None => false,
                },
                None => false,
            };
            if pending && task_due {
                due.push(echod_kernel::ident::clone_string(&p.id));
            }
            i += 1;
        }
        let mut d: usize = 0;
        while d < due.len()
            invariant
                d <= due@.len(),
                s.wf(), inv(now as nat, s@), reach(now as nat, old(s)@, s@), s@.schedules == old(s)@.schedules, now <= MAX_TIME, cfg.wf(),
            decreases due@.len() - d,
        {
            let ghost b = s@;
            s.process_retry_timeout(&TaskRetryTimeoutReq { id: echod_kernel::ident::clone_string(&due[d]) }, now, cfg);
            proof { lemma_reach_step(now as nat, old(s)@, b, s@); }
            did = true;
            d += 1;
        }
        if !did {
            return;
        }
    }
}

} // verus!
