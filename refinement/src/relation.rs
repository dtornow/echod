//! The relation between a kernel document and an Abstract state, and how
//! each Abstract writer effect moves it.
//!
//! The kernel keeps an origin's objects as a map from id to fused row
//! (`echod_kernel::store::AState`); the Abstract model keeps a list of
//! objects addressed by first match (`spec_find_object`). The relation says
//! the two agree at every id, in both directions. The lemmas say that a
//! kernel `insert` and the Abstract effect that writes the same thing keep
//! them agreeing. Everything the handlers do to state is one of these.

use vstd::prelude::*;

use echod_abstract::state as abs_state;
use echod_abstract::state::{AEffect, AObject, AState, spec_find_object, spec_find_object_at, spec_find_schedule, spec_find_schedule_at, spec_without_object, spec_without_schedule, spec_set_task};
use echod_abstract::types as abs;
use echod_kernel::store::AState as KState;
use echod_kernel::types::{APromise, ASchedule, ATask};

use crate::bridge::*;
use crate::*;

verus! {

// ---------------------------------------------------------------------------
// Doors on ids
// ---------------------------------------------------------------------------

pub open spec fn canonical_list(xs: Seq<Chars>) -> bool {
    forall|i: int| 0 <= i < xs.len() ==> canonical(#[trigger] xs[i])
}

pub open spec fn canonical_task(t: ATask) -> bool {
    canonical_list(t.resumes)
}

pub open spec fn canonical_promise(p: APromise) -> bool {
    &&& canonical(p.id)
    &&& canonical_list(p.callbacks)
    &&& match p.task { Some(t) => canonical_task(t), None => true }
}

pub open spec fn canonical_schedule(c: ASchedule) -> bool {
    canonical(c.id) && canonical(c.promise_id)
}

// ---------------------------------------------------------------------------
// The relation
// ---------------------------------------------------------------------------

/// Some kernel id maps to the Abstract id.
pub open spec fn from_kernel_object(k: Map<Chars, APromise>, aid: abs::AIdent) -> bool {
    exists|id: Chars| #[trigger] k.contains_key(id) && ident(id) == aid
}

pub open spec fn from_kernel_schedule(k: Map<Chars, ASchedule>, aid: abs::AIdent) -> bool {
    exists|id: Chars| #[trigger] k.contains_key(id) && ident(id) == aid
}

pub open spec fn objects_related(k: Map<Chars, APromise>, rows: Seq<AObject>) -> bool {
    &&& forall|id: Chars| #[trigger] k.contains_key(id)
        ==> k[id].id == id && canonical_promise(k[id])
            && spec_find_object(rows, ident(id)) == Some(object(k[id]))
    &&& forall|i: int| 0 <= i < rows.len() ==> from_kernel_object(k, #[trigger] rows[i].id)
}

pub open spec fn schedules_related(k: Map<Chars, ASchedule>, rows: Seq<abs::ASchedule>) -> bool {
    &&& forall|id: Chars| #[trigger] k.contains_key(id)
        ==> k[id].id == id && canonical_schedule(k[id])
            && spec_find_schedule(rows, ident(id)) == Some(schedule(k[id]))
    &&& forall|i: int| 0 <= i < rows.len() ==> from_kernel_schedule(k, #[trigger] rows[i].id)
}

/// A kernel document and an Abstract state agree on every object and every
/// schedule. The outbox is not state here: a document carries none, and
/// what a step emits is compared as an observation.
pub open spec fn doc_related(k: KState, a: AState) -> bool {
    &&& objects_related(k.objects, a.objects)
    &&& schedules_related(k.schedules, a.schedules)
}

pub open spec fn task_opt(t: Option<ATask>) -> Option<abs_state::ATaskObject> {
    match t {
        Some(t) => Some(task(t)),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// First match over the Abstract list operations
// ---------------------------------------------------------------------------

proof fn lemma_find_at_shift(rows: Seq<AObject>, x: AObject, aid: abs::AIdent, k: nat)
    ensures spec_find_object_at(seq![x] + rows, aid, k + 1) == spec_find_object_at(rows, aid, k),
    decreases rows.len() - k,
{
    let all = seq![x] + rows;
    if k < rows.len() {
        assert(all[k as int + 1] == rows[k as int]);
        if rows[k as int].id != aid {
            lemma_find_at_shift(rows, x, aid, k + 1);
        }
    }
}

pub proof fn lemma_find_prepend(rows: Seq<AObject>, x: AObject, aid: abs::AIdent)
    ensures spec_find_object(seq![x] + rows, aid)
        == if x.id == aid { Some(x) } else { spec_find_object(rows, aid) },
{
    let all = seq![x] + rows;
    assert(all[0] == x);
    if x.id != aid {
        lemma_find_at_shift(rows, x, aid, 0);
    }
}

pub proof fn lemma_find_cons(rows: Seq<AObject>, aid: abs::AIdent)
    requires rows.len() > 0,
    ensures spec_find_object(rows, aid)
        == if rows[0].id == aid { Some(rows[0]) } else { spec_find_object(rows.drop_first(), aid) },
{
    assert(rows =~= seq![rows[0]] + rows.drop_first());
    lemma_find_prepend(rows.drop_first(), rows[0], aid);
}

pub proof fn lemma_find_without(rows: Seq<AObject>, removed: abs::AIdent, aid: abs::AIdent)
    ensures spec_find_object(spec_without_object(rows, removed), aid)
        == if aid == removed { None } else { spec_find_object(rows, aid) },
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_find_cons(rows, aid);
        lemma_find_without(rows.drop_first(), removed, aid);
        if rows[0].id == removed {
        } else {
            lemma_find_prepend(spec_without_object(rows.drop_first(), removed), rows[0], aid);
        }
    }
}

pub proof fn lemma_without_ids(rows: Seq<AObject>, removed: abs::AIdent)
    ensures forall|i: int| 0 <= i < spec_without_object(rows, removed).len()
        ==> #[trigger] spec_without_object(rows, removed)[i].id != removed
            && exists|j: int| 0 <= j < rows.len() && rows[j].id == spec_without_object(rows, removed)[i].id,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let rest = rows.drop_first();
        lemma_without_ids(rest, removed);
        let out = spec_without_object(rows, removed);
        if rows[0].id == removed {
            assert forall|i: int| 0 <= i < out.len()
                implies #[trigger] out[i].id != removed
                    && exists|j: int| 0 <= j < rows.len() && rows[j].id == out[i].id by {
                assert(out[i] == spec_without_object(rest, removed)[i]);
                let j = choose|j: int| 0 <= j < rest.len() && rest[j].id == out[i].id;
                assert(rows[j + 1].id == out[i].id);
            }
        } else {
            assert forall|i: int| 0 <= i < out.len()
                implies #[trigger] out[i].id != removed
                    && exists|j: int| 0 <= j < rows.len() && rows[j].id == out[i].id by {
                if i == 0 {
                    assert(out[0] == rows[0]);
                } else {
                    assert(out[i] == spec_without_object(rest, removed)[i - 1]);
                    let j = choose|j: int| 0 <= j < rest.len() && rest[j].id == out[i].id;
                    assert(rows[j + 1].id == out[i].id);
                }
            }
        }
    }
}

pub proof fn lemma_set_task_shape(rows: Seq<AObject>, tid: abs::AIdent, t: abs_state::ATaskObject)
    ensures
        spec_set_task(rows, tid, t).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] spec_set_task(rows, tid, t)[i]
            == if rows[i].id == tid { AObject { task: Some(t), ..rows[i] } } else { rows[i] },
    decreases rows.len(),
{
    if rows.len() > 0 {
        let rest = rows.drop_first();
        lemma_set_task_shape(rest, tid, t);
        let out = spec_set_task(rows, tid, t);
        assert forall|i: int| 0 <= i < rows.len() implies #[trigger] out[i]
            == if rows[i].id == tid { AObject { task: Some(t), ..rows[i] } } else { rows[i] } by {
            if i > 0 {
                assert(out[i] == spec_set_task(rest, tid, t)[i - 1]);
                assert(rest[i - 1] == rows[i]);
            }
        }
    }
}

proof fn lemma_find_at_pointwise(rows: Seq<AObject>, rows2: Seq<AObject>, aid: abs::AIdent, k: nat, f: spec_fn(AObject) -> AObject)
    requires
        rows2.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] rows2[i] == f(rows[i]) && rows2[i].id == rows[i].id,
    ensures spec_find_object_at(rows2, aid, k) == match spec_find_object_at(rows, aid, k) {
        Some(o) => Some(f(o)),
        None => None,
    },
    decreases rows.len() - k,
{
    if k < rows.len() {
        if rows[k as int].id != aid {
            lemma_find_at_pointwise(rows, rows2, aid, k + 1, f);
        }
    }
}

pub proof fn lemma_find_set_task(rows: Seq<AObject>, tid: abs::AIdent, t: abs_state::ATaskObject, aid: abs::AIdent)
    ensures spec_find_object(spec_set_task(rows, tid, t), aid) == match spec_find_object(rows, aid) {
        Some(o) => Some(if aid == tid { AObject { task: Some(t), ..o } } else { o }),
        None => None,
    },
{
    lemma_set_task_shape(rows, tid, t);
    let f = |o: AObject| if o.id == tid { AObject { task: Some(t), ..o } } else { o };
    lemma_find_at_pointwise(rows, spec_set_task(rows, tid, t), aid, 0, f);
    match spec_find_object(rows, aid) {
        Some(o) => { lemma_find_id(rows, aid); }
        None => {}
    }
}

/// What first match returns carries the id asked for.
pub proof fn lemma_find_id(rows: Seq<AObject>, aid: abs::AIdent)
    ensures match spec_find_object(rows, aid) { Some(o) => o.id == aid, None => true },
{
    lemma_find_at_id(rows, aid, 0);
}

proof fn lemma_find_at_id(rows: Seq<AObject>, aid: abs::AIdent, k: nat)
    ensures match spec_find_object_at(rows, aid, k) { Some(o) => o.id == aid, None => true },
    decreases rows.len() - k,
{
    if k < rows.len() && rows[k as int].id != aid {
        lemma_find_at_id(rows, aid, k + 1);
    }
}

/// First match finds something exactly when some row carries the id.
pub proof fn lemma_find_some(rows: Seq<AObject>, aid: abs::AIdent)
    ensures (spec_find_object(rows, aid) is Some) == exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i].id == aid,
{
    lemma_find_at_some(rows, aid, 0);
}

proof fn lemma_find_at_some(rows: Seq<AObject>, aid: abs::AIdent, k: nat)
    ensures (spec_find_object_at(rows, aid, k) is Some) == exists|i: int| k <= i < rows.len() && #[trigger] rows[i].id == aid,
    decreases rows.len() - k,
{
    if k < rows.len() {
        if rows[k as int].id == aid {
            assert(rows[k as int].id == aid);
        } else {
            lemma_find_at_some(rows, aid, k + 1);
        }
    }
}

// Schedules: the same three shapes.

proof fn lemma_find_sched_at_shift(rows: Seq<abs::ASchedule>, x: abs::ASchedule, aid: abs::AIdent, k: nat)
    ensures spec_find_schedule_at(seq![x] + rows, aid, k + 1) == spec_find_schedule_at(rows, aid, k),
    decreases rows.len() - k,
{
    let all = seq![x] + rows;
    if k < rows.len() {
        assert(all[k as int + 1] == rows[k as int]);
        if rows[k as int].id != aid {
            lemma_find_sched_at_shift(rows, x, aid, k + 1);
        }
    }
}

pub proof fn lemma_find_sched_prepend(rows: Seq<abs::ASchedule>, x: abs::ASchedule, aid: abs::AIdent)
    ensures spec_find_schedule(seq![x] + rows, aid)
        == if x.id == aid { Some(x) } else { spec_find_schedule(rows, aid) },
{
    let all = seq![x] + rows;
    assert(all[0] == x);
    if x.id != aid {
        lemma_find_sched_at_shift(rows, x, aid, 0);
    }
}

pub proof fn lemma_find_sched_cons(rows: Seq<abs::ASchedule>, aid: abs::AIdent)
    requires rows.len() > 0,
    ensures spec_find_schedule(rows, aid)
        == if rows[0].id == aid { Some(rows[0]) } else { spec_find_schedule(rows.drop_first(), aid) },
{
    assert(rows =~= seq![rows[0]] + rows.drop_first());
    lemma_find_sched_prepend(rows.drop_first(), rows[0], aid);
}

pub proof fn lemma_find_sched_without(rows: Seq<abs::ASchedule>, removed: abs::AIdent, aid: abs::AIdent)
    ensures spec_find_schedule(spec_without_schedule(rows, removed), aid)
        == if aid == removed { None } else { spec_find_schedule(rows, aid) },
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_find_sched_cons(rows, aid);
        lemma_find_sched_without(rows.drop_first(), removed, aid);
        if rows[0].id == removed {
        } else {
            lemma_find_sched_prepend(spec_without_schedule(rows.drop_first(), removed), rows[0], aid);
        }
    }
}

pub proof fn lemma_sched_without_ids(rows: Seq<abs::ASchedule>, removed: abs::AIdent)
    ensures forall|i: int| 0 <= i < spec_without_schedule(rows, removed).len()
        ==> #[trigger] spec_without_schedule(rows, removed)[i].id != removed
            && exists|j: int| 0 <= j < rows.len() && rows[j].id == spec_without_schedule(rows, removed)[i].id,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let rest = rows.drop_first();
        lemma_sched_without_ids(rest, removed);
        let out = spec_without_schedule(rows, removed);
        if rows[0].id == removed {
            assert forall|i: int| 0 <= i < out.len()
                implies #[trigger] out[i].id != removed
                    && exists|j: int| 0 <= j < rows.len() && rows[j].id == out[i].id by {
                assert(out[i] == spec_without_schedule(rest, removed)[i]);
                let j = choose|j: int| 0 <= j < rest.len() && rest[j].id == out[i].id;
                assert(rows[j + 1].id == out[i].id);
            }
        } else {
            assert forall|i: int| 0 <= i < out.len()
                implies #[trigger] out[i].id != removed
                    && exists|j: int| 0 <= j < rows.len() && rows[j].id == out[i].id by {
                if i == 0 {
                    assert(out[0] == rows[0]);
                } else {
                    assert(out[i] == spec_without_schedule(rest, removed)[i - 1]);
                    let j = choose|j: int| 0 <= j < rest.len() && rest[j].id == out[i].id;
                    assert(rows[j + 1].id == out[i].id);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The effects, as moves of the relation
// ---------------------------------------------------------------------------

/// `SetPromise` at `ident(id)` with the kernel row `p`'s promise face, when
/// `p`'s task is what the Abstract object already holds (or none, if the id is
/// new): the kernel inserts `p`.
pub proof fn lemma_set_promise(k: Map<Chars, APromise>, rows: Seq<AObject>, id: Chars, p: APromise)
    requires
        objects_related(k, rows),
        canonical_promise(p),
        p.id == id,
        task_opt(p.task) == match spec_find_object(rows, ident(id)) { Some(o) => o.task, None => None },
    ensures
        objects_related(
            k.insert(id, p),
            seq![AObject { id: ident(id), promise: promise(p), task: match spec_find_object(rows, ident(id)) { Some(o) => o.task, None => None } }]
                + spec_without_object(rows, ident(id)),
        ),
{
    let aid = ident(id);
    let head = AObject { id: aid, promise: promise(p), task: match spec_find_object(rows, aid) { Some(o) => o.task, None => None } };
    let out = seq![head] + spec_without_object(rows, aid);
    let k2 = k.insert(id, p);
    assert(head == object(p));
    assert forall|x: Chars| #[trigger] k2.contains_key(x)
        implies k2[x].id == x && canonical_promise(k2[x]) && spec_find_object(out, ident(x)) == Some(object(k2[x])) by {
        lemma_find_prepend(spec_without_object(rows, aid), head, ident(x));
        if x == id {
        } else {
            assert(k.contains_key(x));
            if ident(x) == aid {
                lemma_ident_injective(x, id);
                assert(false);
            }
            lemma_find_without(rows, aid, ident(x));
        }
    }
    lemma_without_ids(rows, aid);
    assert forall|i: int| 0 <= i < out.len() implies from_kernel_object(k2, #[trigger] out[i].id) by {
        if i == 0 {
            assert(k2.contains_key(id) && ident(id) == out[0].id);
        } else {
            let o = spec_without_object(rows, aid)[i - 1];
            assert(out[i] == o);
            let j = choose|j: int| 0 <= j < rows.len() && rows[j].id == o.id;
            assert(from_kernel_object(k, rows[j].id));
            let x = choose|x: Chars| #[trigger] k.contains_key(x) && ident(x) == rows[j].id;
            assert(k2.contains_key(x) && ident(x) == out[i].id);
        }
    }
}

/// `SetTask` at `ident(id)` with the task `t`: the kernel inserts the row
/// with `t` as its task.
pub proof fn lemma_set_task(k: Map<Chars, APromise>, rows: Seq<AObject>, id: Chars, t: ATask)
    requires
        objects_related(k, rows),
        k.contains_key(id),
        canonical_task(t),
    ensures
        objects_related(k.insert(id, k[id].with_task(t)), spec_set_task(rows, ident(id), task(t))),
{
    let aid = ident(id);
    let out = spec_set_task(rows, aid, task(t));
    let k2 = k.insert(id, k[id].with_task(t));
    lemma_set_task_shape(rows, aid, task(t));
    assert forall|x: Chars| #[trigger] k2.contains_key(x)
        implies k2[x].id == x && canonical_promise(k2[x]) && spec_find_object(out, ident(x)) == Some(object(k2[x])) by {
        lemma_find_set_task(rows, aid, task(t), ident(x));
        if x == id {
            assert(object(k[id].with_task(t)) == AObject { task: Some(task(t)), ..object(k[id]) });
        } else {
            assert(k.contains_key(x));
            if ident(x) == aid {
                lemma_ident_injective(x, id);
                assert(false);
            }
        }
    }
    assert forall|i: int| 0 <= i < out.len() implies from_kernel_object(k2, #[trigger] out[i].id) by {
        assert(out[i].id == rows[i].id);
        let x = choose|x: Chars| #[trigger] k.contains_key(x) && ident(x) == rows[i].id;
        assert(k2.contains_key(x) && ident(x) == out[i].id);
    }
}

/// `SetSchedule` writes `c`: the kernel inserts it.
pub proof fn lemma_set_schedule(k: Map<Chars, ASchedule>, rows: Seq<abs::ASchedule>, c: ASchedule)
    requires
        schedules_related(k, rows),
        canonical_schedule(c),
    ensures
        schedules_related(k.insert(c.id, c), seq![schedule(c)] + spec_without_schedule(rows, ident(c.id))),
{
    let aid = ident(c.id);
    let out = seq![schedule(c)] + spec_without_schedule(rows, aid);
    let k2 = k.insert(c.id, c);
    assert forall|x: Chars| #[trigger] k2.contains_key(x)
        implies k2[x].id == x && canonical_schedule(k2[x]) && spec_find_schedule(out, ident(x)) == Some(schedule(k2[x])) by {
        lemma_find_sched_prepend(spec_without_schedule(rows, aid), schedule(c), ident(x));
        if x == c.id {
        } else {
            assert(k.contains_key(x));
            if ident(x) == aid {
                lemma_ident_injective(x, c.id);
                assert(false);
            }
            lemma_find_sched_without(rows, aid, ident(x));
        }
    }
    lemma_sched_without_ids(rows, aid);
    assert forall|i: int| 0 <= i < out.len() implies from_kernel_schedule(k2, #[trigger] out[i].id) by {
        if i == 0 {
            assert(k2.contains_key(c.id) && ident(c.id) == out[0].id);
        } else {
            let o = spec_without_schedule(rows, aid)[i - 1];
            assert(out[i] == o);
            let j = choose|j: int| 0 <= j < rows.len() && rows[j].id == o.id;
            assert(from_kernel_schedule(k, rows[j].id));
            let x = choose|x: Chars| #[trigger] k.contains_key(x) && ident(x) == rows[j].id;
            assert(k2.contains_key(x) && ident(x) == out[i].id);
        }
    }
}

/// `DeleteSchedule` at `ident(id)`: the kernel removes `id`.
pub proof fn lemma_delete_schedule(k: Map<Chars, ASchedule>, rows: Seq<abs::ASchedule>, id: Chars)
    requires
        schedules_related(k, rows),
        canonical(id),
    ensures
        schedules_related(k.remove(id), spec_without_schedule(rows, ident(id))),
{
    let aid = ident(id);
    let out = spec_without_schedule(rows, aid);
    let k2 = k.remove(id);
    assert forall|x: Chars| #[trigger] k2.contains_key(x)
        implies k2[x].id == x && canonical_schedule(k2[x]) && spec_find_schedule(out, ident(x)) == Some(schedule(k2[x])) by {
        assert(k.contains_key(x) && x != id);
        if ident(x) == aid {
            lemma_ident_injective(x, id);
            assert(false);
        }
        lemma_find_sched_without(rows, aid, ident(x));
    }
    lemma_sched_without_ids(rows, aid);
    assert forall|i: int| 0 <= i < out.len() implies from_kernel_schedule(k2, #[trigger] out[i].id) by {
        let j = choose|j: int| 0 <= j < rows.len() && rows[j].id == out[i].id;
        assert(from_kernel_schedule(k, rows[j].id));
        let x = choose|x: Chars| #[trigger] k.contains_key(x) && ident(x) == rows[j].id;
        if x == id {
            assert(out[i].id == aid);
            assert(false);
        }
        assert(k2.contains_key(x) && ident(x) == out[i].id);
    }
}

/// An Abstract id present in the list has a kernel row behind it.
pub proof fn lemma_related_lookup(k: Map<Chars, APromise>, rows: Seq<AObject>, aid: abs::AIdent)
    requires objects_related(k, rows),
    ensures
        (spec_find_object(rows, aid) is Some) ==> exists|id: Chars| #[trigger] k.contains_key(id) && ident(id) == aid,
{
    lemma_find_some(rows, aid);
    if spec_find_object(rows, aid) is Some {
        let i = choose|i: int| 0 <= i < rows.len() && #[trigger] rows[i].id == aid;
        assert(from_kernel_object(k, rows[i].id));
    }
}

/// The kernel has `id` exactly when the Abstract list has `ident(id)`.
pub proof fn lemma_related_contains(k: Map<Chars, APromise>, rows: Seq<AObject>, id: Chars)
    requires objects_related(k, rows), canonical(id),
    ensures k.contains_key(id) == (spec_find_object(rows, ident(id)) is Some),
{
    lemma_related_lookup(k, rows, ident(id));
    if spec_find_object(rows, ident(id)) is Some {
        let x = choose|x: Chars| #[trigger] k.contains_key(x) && ident(x) == ident(id);
        lemma_ident_injective(x, id);
    }
}

pub proof fn lemma_sched_related_contains(k: Map<Chars, ASchedule>, rows: Seq<abs::ASchedule>, id: Chars)
    requires schedules_related(k, rows), canonical(id),
    ensures k.contains_key(id) == (spec_find_schedule(rows, ident(id)) is Some),
{
    lemma_find_sched_some(rows, ident(id));
    if spec_find_schedule(rows, ident(id)) is Some {
        let i = choose|i: int| 0 <= i < rows.len() && #[trigger] rows[i].id == ident(id);
        assert(from_kernel_schedule(k, rows[i].id));
        let x = choose|x: Chars| #[trigger] k.contains_key(x) && ident(x) == ident(id);
        lemma_ident_injective(x, id);
    }
}

pub proof fn lemma_find_sched_some(rows: Seq<abs::ASchedule>, aid: abs::AIdent)
    ensures (spec_find_schedule(rows, aid) is Some) == exists|i: int| 0 <= i < rows.len() && #[trigger] rows[i].id == aid,
{
    lemma_find_sched_at_some(rows, aid, 0);
}

proof fn lemma_find_sched_at_some(rows: Seq<abs::ASchedule>, aid: abs::AIdent, k: nat)
    ensures (spec_find_schedule_at(rows, aid, k) is Some) == exists|i: int| k <= i < rows.len() && #[trigger] rows[i].id == aid,
    decreases rows.len() - k,
{
    if k < rows.len() {
        if rows[k as int].id == aid {
            assert(rows[k as int].id == aid);
        } else {
            lemma_find_sched_at_some(rows, aid, k + 1);
        }
    }
}

} // verus!
