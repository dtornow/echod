//! The fleet refines the Abstract: every behaviour of the system model —
//! many nodes over one bucket, crashes, lost acknowledgements, the commit
//! protocol — serves its requests as some run of the Abstract does.
//!
//! The bucket's documents, read together, are one kernel state (`bucket`):
//! every object in its origin's document, every schedule in its own. The
//! relation to the Abstract is `doc_related` on that state, and the
//! observable claim is on the log: the responses served so far are the
//! responses of an Abstract run that ends related to the bucket
//! (`explains`). Each step of the fleet either leaves the bucket and the
//! log alone, or commits one document's kernel step, which is a kernel step
//! on the bucket by locality (`local`), and so an Abstract run by the
//! document-level simulation (`trace`).
//!
//! The statement is under `in_domain`: the wire's numeric bounds, the
//! request doors, a heartbeat's refs of one origin, a well-formed id for
//! each occurrence's promise — and `schedule_held`, that a fire's schedule
//! document is as the fire read it until the promise's commit. The last is
//! a real hypothesis on behaviours: the fleet commits the promise without
//! re-reading the schedule, so another node may delete the schedule in
//! between, and then the promise is one the Abstract never creates.

use vstd::prelude::*;

use echod_abstract::state::AState;
use echod_kernel::external as kext;
use echod_kernel::internal as kint;
use echod_kernel::properties as kprops;
use echod_kernel::steps as ksteps;
use echod_kernel::steps::{full, strip, joint, objects_only, schedules_only, Doc, empty_doc};
use echod_kernel::store::{object_order, AState as KState};
use echod_kernel::types as kernel;
use echod_kernel::types::{origin, AOccurrence, APromise, ARequest, AResponse, ASchedule};
use echod_kernel::node::{Id, Origin};
use echod_kernel::commit::*;
use echod_system::model::*;
use echod_system::theorems as sys;
use echod_system::tla::defs::*;
use echod_system::tla::rules::*;

use crate::actions::*;
use crate::bridge::canonical;
use crate::fire_sim::*;
use crate::heartbeat_sim::canonical_refs;
use crate::local::*;
use crate::promise_sim::create_in_domain;
use crate::relation::*;
use crate::schedule_sim::schedule_create_in_domain;
use crate::suspend_sim::canonical_actions;
use crate::sweep_sim::*;
use crate::task_sim::{doc_headroom, fence_in_domain};
use crate::trace::*;
use crate::*;

verus! {

// ---------------------------------------------------------------------------
// The bucket as one kernel state
// ---------------------------------------------------------------------------

/// The ids of every document's objects, each read back to its origin.
pub open spec fn bucket_obj_dom(s: Cluster) -> Set<Chars> {
    s.store.docs.dom().map_flatten_by(|o: Origin| s.store.docs[o].objects.dom(), |id: Chars| origin(id))
}

/// The ids of every document's schedules, each read back to its document.
pub open spec fn bucket_sch_dom(s: Cluster) -> Set<Chars> {
    s.store.docs.dom().map_flatten_by(|o: Origin| s.store.docs[o].schedules.dom(), |sid: Chars| sched_target(sid))
}

/// Every object, read from its origin's document.
pub open spec fn bucket_objects(s: Cluster) -> Map<Chars, APromise> {
    Map::new(bucket_obj_dom(s), |id: Chars| s.store.doc(origin(id)).objects[id])
}

/// Every schedule, read from its own document.
pub open spec fn bucket_schedules(s: Cluster) -> Map<Chars, ASchedule> {
    Map::new(bucket_sch_dom(s), |sid: Chars| s.store.doc(sched_target(sid)).schedules[sid])
}

pub open spec fn bucket(s: Cluster) -> KState {
    KState { objects: bucket_objects(s), schedules: bucket_schedules(s), outbox: Map::empty() }
}

/// Every document holds only what is named for it: an origin's document
/// its origin's objects, a schedule's document its schedule.
pub open spec fn partitioned(s: Cluster) -> bool {
    &&& forall|o: Origin, id: Chars| #[trigger] s.store.docs.contains_key(o) && #[trigger] s.store.docs[o].objects.contains_key(id) ==> origin(id) == o
    &&& forall|o: Origin, sid: Chars| #[trigger] s.store.docs.contains_key(o) && #[trigger] s.store.docs[o].schedules.contains_key(sid) ==> sched_target(sid) == o
}

/// What the bucket has, when the store is partitioned: an id is in the
/// bucket exactly when its origin's document has it, read from there.
pub proof fn lemma_bucket_has(s: Cluster)
    requires partitioned(s),
    ensures
        forall|id: Chars| #[trigger] bucket_objects(s).contains_key(id) <==> s.store.doc(origin(id)).objects.contains_key(id),
        forall|id: Chars| #[trigger] bucket_objects(s).contains_key(id) ==> bucket_objects(s)[id] == s.store.doc(origin(id)).objects[id],
        forall|sid: Chars| #[trigger] bucket_schedules(s).contains_key(sid) <==> s.store.doc(sched_target(sid)).schedules.contains_key(sid),
        forall|sid: Chars| #[trigger] bucket_schedules(s).contains_key(sid) ==> bucket_schedules(s)[sid] == s.store.doc(sched_target(sid)).schedules[sid],
{
    let docs = s.store.docs;
    let fo = |o: Origin| docs[o].objects.dom();
    let ro = |id: Chars| origin(id);
    let fs = |o: Origin| docs[o].schedules.dom();
    let rs = |sid: Chars| sched_target(sid);
    assert forall|o: Origin, id: Chars| #[trigger] docs.dom().contains(o) && fo(o).contains(id) implies #[trigger] ro(id) == o by {
        assert(docs.contains_key(o) && docs[o].objects.contains_key(id));
    }
    assert forall|o: Origin, sid: Chars| #[trigger] docs.dom().contains(o) && fs(o).contains(sid) implies #[trigger] rs(sid) == o by {
        assert(docs.contains_key(o) && docs[o].schedules.contains_key(sid));
    }
    assert forall|id: Chars| #[trigger] bucket_objects(s).contains_key(id) <==> s.store.doc(origin(id)).objects.contains_key(id) by {
        docs.dom().lemma_map_flatten_by_contains(fo, ro, id);
    }
    assert forall|sid: Chars| #[trigger] bucket_schedules(s).contains_key(sid) <==> s.store.doc(sched_target(sid)).schedules.contains_key(sid) by {
        docs.dom().lemma_map_flatten_by_contains(fs, rs, sid);
    }
}

/// The schedule ids of one document.
pub open spec fn sched_in(o: Origin) -> Ids {
    |sid: Chars| sched_target(sid) == o
}

/// A document's content is inside its name.
pub open spec fn doc_inside(d: Doc, o: Origin) -> bool {
    inside_obj(full(d), in_origin(o)) && inside_sch(full(d), sched_in(o))
}

pub proof fn lemma_partitioned_doc(s: Cluster, o: Origin)
    requires partitioned(s),
    ensures doc_inside(s.store.doc(o), o),
{
}

/// The bucket's objects not in `f` and schedules not in `g`: the rest of
/// the bucket beside the documents those name.
pub open spec fn rest(s: Cluster, f: Ids, g: Ids) -> KState {
    KState {
        objects: bucket_objects(s).filter_keys(|id: Chars| !f(id)),
        schedules: bucket_schedules(s).filter_keys(|sid: Chars| !g(sid)),
        outbox: Map::empty(),
    }
}

/// The bucket is `k` beside the rest, when `k` is exactly the bucket's part
/// inside `f` and `g`.
pub proof fn lemma_split(s: Cluster, f: Ids, g: Ids, k: KState)
    requires
        partitioned(s),
        k.outbox == Map::<kernel::OutboxKey, kernel::AOutboxEntry>::empty(),
        forall|id: Chars| #[trigger] k.objects.contains_key(id) <==> bucket_objects(s).contains_key(id) && f(id),
        forall|id: Chars| #[trigger] k.objects.contains_key(id) ==> k.objects[id] == bucket_objects(s)[id],
        forall|sid: Chars| #[trigger] k.schedules.contains_key(sid) <==> bucket_schedules(s).contains_key(sid) && g(sid),
        forall|sid: Chars| #[trigger] k.schedules.contains_key(sid) ==> k.schedules[sid] == bucket_schedules(s)[sid],
    ensures
        bucket(s) == glue(k, rest(s, f, g)),
        inside_obj(k, f), inside_sch(k, g),
        outside_obj(rest(s, f, g), f), outside_sch(rest(s, f, g), g),
{
    lemma_bucket_has(s);
    let r = rest(s, f, g);
    assert(bucket(s).objects =~= glue(k, r).objects);
    assert(bucket(s).schedules =~= glue(k, r).schedules);
}

/// An origin's document is the bucket's part inside its origin.
pub proof fn lemma_doc_part(s: Cluster, o: Origin)
    requires partitioned(s),
    ensures ({
        let k = full(s.store.doc(o));
        &&& forall|id: Chars| #[trigger] k.objects.contains_key(id) <==> bucket_objects(s).contains_key(id) && in_origin(o)(id)
        &&& forall|id: Chars| #[trigger] k.objects.contains_key(id) ==> k.objects[id] == bucket_objects(s)[id]
        &&& forall|sid: Chars| #[trigger] k.schedules.contains_key(sid) <==> bucket_schedules(s).contains_key(sid) && sched_in(o)(sid)
        &&& forall|sid: Chars| #[trigger] k.schedules.contains_key(sid) ==> k.schedules[sid] == bucket_schedules(s)[sid]
    }),
{
    lemma_bucket_has(s);
    let k = full(s.store.doc(o));
    assert forall|id: Chars| #[trigger] k.objects.contains_key(id) implies bucket_objects(s).contains_key(id) && in_origin(o)(id) && k.objects[id] == bucket_objects(s)[id] by {
        assert(s.store.docs.contains_key(o));
        assert(origin(id) == o);
    }
    assert forall|sid: Chars| #[trigger] k.schedules.contains_key(sid) implies bucket_schedules(s).contains_key(sid) && sched_in(o)(sid) && k.schedules[sid] == bucket_schedules(s)[sid] by {
        assert(s.store.docs.contains_key(o));
        assert(sched_target(sid) == o);
    }
}

/// The bucket is an origin's document beside the rest.
pub proof fn lemma_split_doc(s: Cluster, o: Origin)
    requires partitioned(s),
    ensures ({
        let k = full(s.store.doc(o));
        let r = rest(s, in_origin(o), sched_in(o));
        &&& bucket(s) == glue(k, r)
        &&& inside_obj(k, in_origin(o)) && inside_sch(k, sched_in(o))
        &&& outside_obj(r, in_origin(o)) && outside_sch(r, sched_in(o))
    }),
{
    lemma_doc_part(s, o);
    lemma_split(s, in_origin(o), sched_in(o), full(s.store.doc(o)));
}

/// The bucket is an origin's objects and a schedule's document beside the
/// rest, when the two documents are shaped for their names.
pub proof fn lemma_split_joint(s: Cluster, o: Origin, st: Origin)
    requires partitioned(s), !is_sched(o), is_sched(st), shaped(o, s.store.doc(o)), shaped(st, s.store.doc(st)),
    ensures ({
        let k = joint(s.store.doc(o), s.store.doc(st));
        let r = rest(s, in_origin(o), sched_in(st));
        &&& bucket(s) == glue(k, r)
        &&& inside_obj(k, in_origin(o)) && inside_sch(k, sched_in(st))
        &&& outside_obj(r, in_origin(o)) && outside_sch(r, sched_in(st))
    }),
{
    lemma_doc_part(s, o);
    lemma_doc_part(s, st);
    lemma_split(s, in_origin(o), sched_in(st), joint(s.store.doc(o), s.store.doc(st)));
}

/// Writing one document moves nothing in the rest beside it.
pub proof fn lemma_rest_write(s: Cluster, s2: Cluster, o: Origin, d: Doc, f: Ids, g: Ids)
    requires
        partitioned(s), partitioned(s2),
        s2.store.docs == s.store.docs.insert(o, d),
        forall|id: Chars| !f(id) ==> origin(id) != o,
        forall|sid: Chars| !g(sid) ==> sched_target(sid) != o,
    ensures rest(s2, f, g) == rest(s, f, g),
{
    lemma_bucket_has(s);
    lemma_bucket_has(s2);
    assert forall|id: Chars| !f(id) implies s2.store.doc(origin(id)) == s.store.doc(origin(id)) by {}
    assert forall|sid: Chars| !g(sid) implies s2.store.doc(sched_target(sid)) == s.store.doc(sched_target(sid)) by {}
    assert(rest(s2, f, g).objects =~= rest(s, f, g).objects);
    assert(rest(s2, f, g).schedules =~= rest(s, f, g).schedules);
}

/// After one document is written with content inside its name, the bucket
/// is partitioned still, and is the new document beside the same rest.
pub proof fn lemma_written_doc(s: Cluster, s2: Cluster, o: Origin, d: Doc)
    requires partitioned(s), doc_inside(d, o), s2.store.docs == s.store.docs.insert(o, d),
    ensures
        partitioned(s2),
        bucket(s2) == glue(full(d), rest(s, in_origin(o), sched_in(o))),
{
    assert forall|q: Origin, id: Chars| #[trigger] s2.store.docs.contains_key(q) && #[trigger] s2.store.docs[q].objects.contains_key(id) implies origin(id) == q by {
        if q != o {
            assert(s.store.docs.contains_key(q) && s.store.docs[q].objects.contains_key(id));
        } else {
            assert(full(d).objects.contains_key(id));
        }
    }
    assert forall|q: Origin, sid: Chars| #[trigger] s2.store.docs.contains_key(q) && #[trigger] s2.store.docs[q].schedules.contains_key(sid) implies sched_target(sid) == q by {
        if q != o {
            assert(s.store.docs.contains_key(q) && s.store.docs[q].schedules.contains_key(sid));
        } else {
            assert(full(d).schedules.contains_key(sid));
        }
    }
    lemma_split_doc(s2, o);
    assert(s2.store.doc(o) == d);
    lemma_rest_write(s, s2, o, d, in_origin(o), sched_in(o));
}

/// After an origin's document is written beside an untouched schedule's,
/// the bucket is the two beside the same rest.
pub proof fn lemma_written_joint(s: Cluster, s2: Cluster, o: Origin, st: Origin, d: Doc)
    requires
        partitioned(s), !is_sched(o), is_sched(st), shaped(o, d), shaped(st, s.store.doc(st)),
        doc_inside(d, o), s2.store.docs == s.store.docs.insert(o, d),
    ensures
        partitioned(s2),
        bucket(s2) == glue(joint(d, s.store.doc(st)), rest(s, in_origin(o), sched_in(st))),
{
    lemma_written_doc(s, s2, o, d);
    assert(s2.store.doc(st) == s.store.doc(st));
    lemma_split_joint(s2, o, st);
    assert forall|sid: Chars| !sched_in(st)(sid) implies sched_target(sid) != o by {
        if sched_target(sid) == o {
            assert(is_sched(sched_target(sid))) by { lemma_sched_target_is_sched(sid); }
        }
    }
    lemma_rest_write(s, s2, o, d, in_origin(o), sched_in(st));
}

pub proof fn lemma_sched_target_is_sched(sid: Chars)
    ensures is_sched(sched_target(sid)),
{
    reveal_strlit("sched:");
    assert(sched_target(sid).take(6) =~= "sched:"@);
}

/// Rewriting a document with its own content leaves the bucket as it is.
pub proof fn lemma_rewritten(s: Cluster, s2: Cluster, o: Origin)
    requires partitioned(s), s2.store.docs == s.store.docs.insert(o, s.store.doc(o)),
    ensures partitioned(s2), bucket(s2) == bucket(s),
{
    assert forall|q: Origin| true implies #[trigger] s2.store.doc(q) == s.store.doc(q) by {}
    assert forall|q: Origin, id: Chars| #[trigger] s2.store.docs.contains_key(q) && #[trigger] s2.store.docs[q].objects.contains_key(id) implies origin(id) == q by {
        if s.store.docs.contains_key(q) {
            assert(s.store.docs[q].objects.contains_key(id));
        } else {
            assert(s2.store.docs[q] == empty_doc());
        }
    }
    assert forall|q: Origin, sid: Chars| #[trigger] s2.store.docs.contains_key(q) && #[trigger] s2.store.docs[q].schedules.contains_key(sid) implies sched_target(sid) == q by {
        if s.store.docs.contains_key(q) {
            assert(s.store.docs[q].schedules.contains_key(sid));
        } else {
            assert(s2.store.docs[q] == empty_doc());
        }
    }
    lemma_bucket_has(s);
    lemma_bucket_has(s2);
    assert(bucket(s2).objects =~= bucket(s).objects);
    assert(bucket(s2).schedules =~= bucket(s).schedules);
}

/// A store with the same documents has the same bucket.
pub proof fn lemma_bucket_same(s: Cluster, s2: Cluster)
    requires partitioned(s), s2.store.docs == s.store.docs,
    ensures partitioned(s2), bucket(s2) == bucket(s),
{
    assert forall|q: Origin| true implies #[trigger] s2.store.doc(q) == s.store.doc(q) by {}
    assert forall|q: Origin, id: Chars| #[trigger] s2.store.docs.contains_key(q) && #[trigger] s2.store.docs[q].objects.contains_key(id) implies origin(id) == q by {
        assert(s.store.docs.contains_key(q) && s.store.docs[q].objects.contains_key(id));
    }
    assert forall|q: Origin, sid: Chars| #[trigger] s2.store.docs.contains_key(q) && #[trigger] s2.store.docs[q].schedules.contains_key(sid) implies sched_target(sid) == q by {
        assert(s.store.docs.contains_key(q) && s.store.docs[q].schedules.contains_key(sid));
    }
    lemma_bucket_has(s);
    lemma_bucket_has(s2);
    assert(bucket(s2).objects =~= bucket(s).objects);
    assert(bucket(s2).schedules =~= bucket(s).schedules);
}

// ---------------------------------------------------------------------------
// What the system invariant says of the bucket
// ---------------------------------------------------------------------------

/// Every document within the wire's bounds: a door on the bucket, where
/// the kernel's `u32` task version and the Lean text's naturals part.
pub open spec fn store_headroom(s: Cluster) -> bool {
    forall|o: Origin| #[trigger] s.store.docs.contains_key(o) ==> doc_headroom(full(s.store.docs[o]))
}

/// An object of the bucket is its origin's document's, and that document
/// satisfies the catalogue at its stamp.
pub proof fn lemma_bucket_object(s: Cluster, id: Chars)
    requires sys::inv()(s), partitioned(s), bucket_objects(s).contains_key(id),
    ensures ({
        let q = origin(id);
        &&& s.store.docs.contains_key(q)
        &&& s.store.docs[q].objects.contains_key(id)
        &&& bucket_objects(s)[id] == s.store.docs[q].objects[id]
        &&& kprops::inv(s.store.stamps[q], full(s.store.docs[q]))
    }),
{
    lemma_bucket_has(s);
    sys::disassemble(s);
    let q = origin(id);
    assert(s.store.doc(q).objects.contains_key(id));
    if !s.store.docs.contains_key(q) {
        assert(s.store.doc(q) == empty_doc());
    }
}

/// A schedule of the bucket is its own document's, which satisfies the
/// catalogue at its stamp.
pub proof fn lemma_bucket_schedule(s: Cluster, sid: Chars)
    requires sys::inv()(s), partitioned(s), bucket_schedules(s).contains_key(sid),
    ensures ({
        let q = sched_target(sid);
        &&& s.store.docs.contains_key(q)
        &&& s.store.docs[q].schedules.contains_key(sid)
        &&& bucket_schedules(s)[sid] == s.store.docs[q].schedules[sid]
        &&& kprops::inv(s.store.stamps[q], full(s.store.docs[q]))
    }),
{
    lemma_bucket_has(s);
    sys::disassemble(s);
    let q = sched_target(sid);
    assert(s.store.doc(q).schedules.contains_key(sid));
    if !s.store.docs.contains_key(q) {
        assert(s.store.doc(q) == empty_doc());
    }
}

/// The catalogue's entries a step needs of a state.
pub proof fn lemma_inv_basics(t: nat, k: KState)
    requires kprops::inv(t, k),
    ensures not_self(k), kprops::kernel_bounds(k), kprops::kernel_sched_bounds(k), k.keyed(),
{
    reveal(kprops::inv);
}

/// A document of one origin satisfying the catalogue has the sweep's shape:
/// its callbacks are of its origin, and no promise is its own callback.
pub proof fn lemma_inv_shape(t: nat, k: KState, o: Origin)
    requires kprops::inv(t, k), inside_obj(k, in_origin(o)),
    ensures sweep_shape(k, in_origin(o)),
{
    reveal(kprops::inv);
    assert forall|id: Chars, y: Chars| #[trigger] k.objects.contains_key(id) && #[trigger] k.objects[id].callbacks.contains(y) implies in_origin(o)(y) by {
        let p = k.objects[id];
        let i = choose|i: int| 0 <= i < p.callbacks.len() && p.callbacks[i] == y;
        assert(kernel::same_origin_spec(p.callbacks[i], p.id));
        assert(p.id == id);
        assert(origin(id) == o);
    }
}

/// What holds of every object of `k` holds of every object of `r` when
/// `r`'s objects are among `k`'s.
pub proof fn lemma_sub_basics(k: KState, r: KState)
    requires
        forall|id: Chars| #[trigger] r.objects.contains_key(id) ==> k.objects.contains_key(id) && r.objects[id] == k.objects[id],
        not_self(k), kprops::kernel_bounds(k), doc_headroom(k),
    ensures not_self(r), kprops::kernel_bounds(r), doc_headroom(r),
{
}

/// The same, of a document glued beside the rest.
pub proof fn lemma_gobj_basics(k: KState, r: KState, c: Map<Chars, ASchedule>)
    requires not_self(k), not_self(r), kprops::kernel_bounds(k), kprops::kernel_bounds(r), doc_headroom(k), doc_headroom(r),
    ensures not_self(gobj(k, r, c)), kprops::kernel_bounds(gobj(k, r, c)), doc_headroom(gobj(k, r, c)),
{
    let g = gobj(k, r, c);
    assert forall|id: Chars| #[trigger] g.objects.contains_key(id) implies
        !g.objects[id].callbacks.contains(id) && kprops::kernel_bounds_at(g.objects[id])
        && match g.objects[id].task { Some(t) => t.version < kernel::MAX_VERSION && t.resumes.len() <= u64::MAX, None => true } by {
        if r.objects.contains_key(id) {
            assert(g.objects[id] == r.objects[id]);
        } else {
            assert(k.objects.contains_key(id) && g.objects[id] == k.objects[id]);
        }
    }
}

/// The bucket has the sweep's and the handlers' doors: from the catalogue
/// on every document, and the headroom door on every document.
pub proof fn lemma_bucket_basics(s: Cluster)
    requires sys::inv()(s), partitioned(s), store_headroom(s),
    ensures not_self(bucket(s)), kprops::kernel_bounds(bucket(s)), doc_headroom(bucket(s)),
{
    let b = bucket(s);
    assert forall|id: Chars| #[trigger] b.objects.contains_key(id) implies
        !b.objects[id].callbacks.contains(id) && kprops::kernel_bounds_at(b.objects[id])
        && match b.objects[id].task { Some(t) => t.version < kernel::MAX_VERSION && t.resumes.len() <= u64::MAX, None => true } by {
        lemma_bucket_object(s, id);
        let q = origin(id);
        let d = full(s.store.docs[q]);
        lemma_inv_basics(s.store.stamps[q], d);
        assert(d.objects.contains_key(id));
        assert(doc_headroom(d));
    }
}

/// The rest beside a document has the bucket's doors.
pub proof fn lemma_rest_basics(s: Cluster, f: Ids, g: Ids)
    requires sys::inv()(s), partitioned(s), store_headroom(s),
    ensures not_self(rest(s, f, g)), kprops::kernel_bounds(rest(s, f, g)), doc_headroom(rest(s, f, g)),
{
    lemma_bucket_basics(s);
    lemma_sub_basics(bucket(s), rest(s, f, g));
}

/// Ids the related state has are canonical.
pub proof fn lemma_related_canonical(k: KState, a: AState, ids: Seq<Chars>)
    requires doc_related(k, a), ids_of(k, ids),
    ensures canonical_ids(ids),
{
    assert forall|i: int| 0 <= i < ids.len() implies canonical(#[trigger] ids[i]) by {
        assert(k.objects.contains_key(ids[i]));
    }
}

/// Every id is an object of `k`.
pub open spec fn ids_of(k: KState, ids: Seq<Chars>) -> bool {
    forall|i: int| 0 <= i < ids.len() ==> k.objects.contains_key(#[trigger] ids[i])
}

/// The relation does not see the outbox.
pub proof fn lemma_related_outbox(k: KState, k2: KState, a: AState)
    requires doc_related(k, a), k2.objects == k.objects, k2.schedules == k.schedules,
    ensures doc_related(k2, a),
{
}

// ---------------------------------------------------------------------------
// A document's steps on the bucket
// ---------------------------------------------------------------------------
//
// Each is the kernel's function on one document beside the rest of the
// bucket: by locality it is the function on the bucket, and by the
// document-level simulation an Abstract run. The outbox is dropped where
// the node drops it — between a request's first sweep and its handler, and
// at the write — and the relation does not see it.

/// The Abstract run a sweep of document `k` beside `r` is.
pub open spec fn sweep_step_actions(k: KState, r: KState, ids: Seq<Chars>, t: u64, rt: u64) -> Seq<AbsAction> {
    lift(sweep_actions(glue(k, r), ids, t, rt), t)
}

pub proof fn lemma_sweep_step(k: KState, r: KState, a: AState, f: Ids, ids: Seq<Chars>, t: u64, rt: u64)
    requires
        doc_related(glue(k, r), a),
        sweep_shape(k, f), outside_obj(r, f), not_self(r),
        ids_of(k, ids),
        t <= kernel::MAX_TIME, rt <= kernel::MAX_TIME,
    ensures ({
        let k2 = ksteps::executable_single_pass(k, ids, t as nat, rt as nat);
        let acts = sweep_step_actions(k, r, ids, t, rt);
        &&& doc_related(glue(full(strip(k2)), r), abs_run(a, acts, rt))
        &&& abs_responses(a, acts, rt) == Seq::<AbsResponse>::empty()
        &&& sweep_shape(k2, f)
        &&& k2.schedules == k.schedules
    }),
{
    let b = glue(k, r);
    let c = k.schedules.union_prefer_right(r.schedules);
    let k2 = ksteps::executable_single_pass(k, ids, t as nat, rt as nat);
    assert forall|i: int| 0 <= i < ids.len() implies f(#[trigger] ids[i]) by {
        assert(k.objects.contains_key(ids[i]));
    }
    lemma_single_pass_local(k, r, c, f, ids, t as nat, rt as nat);
    assert forall|i: int| 0 <= i < ids.len() implies b.objects.contains_key(#[trigger] ids[i]) by {
        assert(k.objects.contains_key(ids[i]));
    }
    lemma_related_canonical(b, a, ids);
    assert(not_self(b)) by {
        assert forall|id: Chars| #[trigger] b.objects.contains_key(id) implies !b.objects[id].callbacks.contains(id) by {
            if r.objects.contains_key(id) {
                assert(b.objects[id] == r.objects[id]);
            } else {
                assert(k.objects.contains_key(id) && b.objects[id] == k.objects[id]);
            }
        }
    }
    let sa = sweep_actions(b, ids, t, rt);
    lemma_sweep_sim(b, a, ids, t, rt);
    lemma_lift_run(a, sa, t, rt);
    let g2 = glue(full(strip(k2)), r);
    assert(g2.objects == gobj(k2, r, c).objects);
    assert(g2.schedules == c);
    lemma_related_outbox(gobj(k2, r, c), g2, abs_run(a, lift(sa, t), rt));
}

/// The door on a request that does not look at the document: its ids
/// canonical, its instants inside the time door, its tags not a targeted
/// timer. With the headroom and bounds doors on the document it is
/// `request_in_domain`.
pub open spec fn request_doors(req: ARequest, now: u64) -> bool {
    match req {
        ARequest::PromiseGet(q) => canonical(q.id),
        ARequest::PromiseCreate(q) => create_in_domain(q),
        ARequest::PromiseSettle(q) => canonical(q.id),
        ARequest::PromiseRegisterCallback(q) => canonical(q.awaited) && canonical(q.awaiter),
        ARequest::PromiseRegisterListener(q) => canonical(q.awaited),
        ARequest::ScheduleGet(q) => canonical(q.id),
        ARequest::ScheduleCreate(q) => schedule_create_in_domain(q, now),
        ARequest::ScheduleDelete(q) => canonical(q.id),
        ARequest::TaskGet(q) => canonical(q.id),
        ARequest::TaskCreate(q) => create_in_domain(q.action) && q.ttl <= kernel::MAX_TIME && now <= kernel::MAX_TIME,
        ARequest::TaskAcquire(q) => canonical(q.id) && q.ttl <= kernel::MAX_TIME && now <= kernel::MAX_TIME,
        ARequest::TaskFulfill(q) => canonical(q.id),
        ARequest::TaskRelease(q) => canonical(q.id),
        ARequest::TaskHalt(q) => canonical(q.id),
        ARequest::TaskContinue(q) => canonical(q.id),
        ARequest::TaskFence(q) => fence_in_domain(q),
        ARequest::TaskFenceCheck(q) => canonical(q.id),
        ARequest::TaskHeartbeat(q) => now <= kernel::MAX_TIME && canonical_refs(q.tasks),
        ARequest::TaskSuspend(q) => canonical(q.id) && canonical_actions(q.actions),
    }
}

pub proof fn lemma_request_doors(k: KState, req: ARequest, now: u64)
    requires request_doors(req, now), doc_headroom(k), kprops::kernel_bounds(k),
    ensures request_in_domain(k, req, now),
{
}

/// A request's ids are inside the document it is served on: its target's
/// origin, or its schedule. A heartbeat's refs are one origin's by the door.
pub proof fn lemma_target_inside(req: ARequest, o: Origin)
    requires
        request_target(req) == Some(o),
        match req { ARequest::TaskHeartbeat(q) => refs_inside(q.tasks, in_origin(o)), _ => true },
    ensures request_inside(req, in_origin(o), sched_in(o)),
{
}

/// The Abstract run a request step — sweep, handler, sweep — on document
/// `k` beside `r` is. `m` is the swept document the handler ran on.
pub open spec fn request_step_actions(k: KState, r: KState, ids1: Seq<Chars>, m: Doc, req: ARequest, ids2: Seq<Chars>, t: u64, rt: u64) -> Seq<AbsAction> {
    let k3 = kext::spec_handle(full(m), req, t as nat).0;
    sweep_step_actions(k, r, ids1, t, rt) + seq![AbsAction::External(request(req), t)] + sweep_step_actions(k3, r, ids2, t, rt)
}

pub proof fn lemma_request_step(k: KState, r: KState, a: AState, o: Origin, ids1: Seq<Chars>, m: Doc, req: ARequest, ids2: Seq<Chars>, t: u64, rt: u64)
    requires
        doc_related(glue(k, r), a),
        kprops::inv(t as nat, k),
        inside_obj(k, in_origin(o)), inside_sch(k, sched_in(o)),
        outside_obj(r, in_origin(o)), outside_sch(r, sched_in(o)),
        not_self(r), kprops::kernel_bounds(r), doc_headroom(r),
        ids_of(k, ids1),
        m == strip(ksteps::executable_single_pass(k, ids1, t as nat, rt as nat)),
        kprops::inv(t as nat, full(m)),
        doc_headroom(full(m)),
        request_doors(req, t), request_inside(req, in_origin(o), sched_in(o)),
        ids_of(kext::spec_handle(full(m), req, t as nat).0, ids2),
        t <= kernel::MAX_TIME, rt <= kernel::MAX_TIME,
    ensures ({
        let (k3, res) = kext::spec_handle(full(m), req, t as nat);
        let new = strip(ksteps::executable_single_pass(k3, ids2, t as nat, rt as nat));
        let acts = request_step_actions(k, r, ids1, m, req, ids2, t, rt);
        &&& doc_related(glue(full(new), r), abs_run(a, acts, rt))
        &&& abs_responses(a, acts, rt) == seq![response(req, res)]
        &&& doc_inside(new, o)
    }),
{
    let f = in_origin(o);
    let g = sched_in(o);
    lemma_in_origin_closed(o);
    lemma_inv_shape(t as nat, k, o);
    // the first sweep
    lemma_sweep_step(k, r, a, f, ids1, t, rt);
    let k1 = ksteps::executable_single_pass(k, ids1, t as nat, rt as nat);
    let acts1 = sweep_step_actions(k, r, ids1, t, rt);
    let a1 = abs_run(a, acts1, rt);
    let km = full(m);
    assert(km == full(strip(k1)));
    assert(doc_related(glue(km, r), a1));
    // the handler, on the swept document with its outbox dropped
    assert(inside_obj(km, f));
    assert(inside_sch(km, g));
    lemma_handle_local(km, r, f, g, req, t as nat);
    let (k3, res) = kext::spec_handle(km, req, t as nat);
    lemma_inv_basics(t as nat, km);
    lemma_gobj_basics(km, r, km.schedules.union_prefer_right(r.schedules));
    lemma_request_doors(glue(km, r), req, t);
    lemma_handle_sim(glue(km, r), a1, req, t);
    let ext = seq![AbsAction::External(request(req), t)];
    lemma_abs_run_external_one(a1, request(req), t, rt);
    let (a2, ares) = external_step(a1, request(req), t);
    assert(doc_related(glue(k3, r), a2));
    assert(response(req, res) == ares);
    // the second sweep, on the handler's state with its outbox
    echod_kernel::external_proof::lemma_spec_handle(t as nat, km, req);
    lemma_inv_shape(t as nat, k3, o);
    lemma_sweep_step(k3, r, a2, f, ids2, t, rt);
    let k4 = ksteps::executable_single_pass(k3, ids2, t as nat, rt as nat);
    let acts3 = sweep_step_actions(k3, r, ids2, t, rt);
    let a3 = abs_run(a2, acts3, rt);
    // the run, assembled
    let acts = request_step_actions(k, r, ids1, m, req, ids2, t, rt);
    assert(acts == (acts1 + ext) + acts3);
    lemma_abs_run_app(a, acts1, ext, rt);
    assert(abs_run(a, acts1 + ext, rt) == a2);
    lemma_abs_run_app(a, acts1 + ext, acts3, rt);
    assert(abs_run(a, acts, rt) == a3);
    assert(abs_responses(a, acts, rt) =~= seq![response(req, res)]);
    // the written document is inside its name
    let new = strip(k4);
    assert(inside_obj(full(new), f));
    assert(full(new).schedules == k3.schedules);
    assert(inside_sch(full(new), g));
}

/// The Abstract run a fire — the occurrence fired, then the origin's sweep
/// — on the origin's objects and the schedule's row `J` beside `r` is.
pub open spec fn fire_step_actions(j: KState, r: KState, sid: Chars, pid: Chars, ids: Seq<Chars>, t: u64, rt: u64) -> Seq<AbsAction> {
    let b = glue(j, r);
    let c = j.schedules[sid];
    let occs = seq![AOccurrence { at: c.next_run_at, promise_id: pid }];
    let f1 = kint::fire_fold(t as nat, j, c, occs, 1);
    lift(fire_actions(b, sid, c, occs, t, 1), t) + lift(sweep_actions(gobj(f1, r, b.schedules), ids, t, rt), t)
}

/// `fire_fold` writes objects only.
pub proof fn lemma_fire_fold_schedules(now: nat, a: KState, c: ASchedule, occs: Seq<AOccurrence>, k: int)
    ensures kint::fire_fold(now, a, c, occs, k).schedules == a.schedules, kint::fire_fold(now, a, c, occs, k).outbox == a.outbox,
    decreases k,
{
    if k > 0 {
        lemma_fire_fold_schedules(now, a, c, occs, k - 1);
    }
}

pub proof fn lemma_fire_step(j: KState, r: KState, a: AState, o: Origin, st: Origin, sid: Chars, pid: Chars, next: u64, ids: Seq<Chars>, t: u64, rt: u64)
    requires
        doc_related(glue(j, r), a),
        kprops::inv(t as nat, j),
        j.outbox == Map::<kernel::OutboxKey, kernel::AOutboxEntry>::empty(),
        inside_obj(j, in_origin(o)), inside_sch(j, sched_in(st)),
        outside_obj(r, in_origin(o)), outside_sch(r, sched_in(st)), not_self(r),
        sched_target(sid) == st,
        j.schedules.contains_key(sid),
        j.schedules[sid].next_run_at <= t,
        j.schedules[sid].next_run_at < next,
        canonical(pid), origin(pid) == o,
        ids_of(kint::spec_fire(j, sid, seq![AOccurrence { at: j.schedules[sid].next_run_at, promise_id: pid }], next, t as nat), ids),
        t <= kernel::MAX_TIME, rt <= kernel::MAX_TIME,
    ensures ({
        let c = j.schedules[sid];
        let fired = kint::spec_fire(j, sid, seq![AOccurrence { at: c.next_run_at, promise_id: pid }], next, t as nat);
        let new = objects_only(ksteps::executable_single_pass(fired, ids, t as nat, rt as nat));
        let acts = fire_step_actions(j, r, sid, pid, ids, t, rt);
        &&& doc_related(glue(KState { objects: new.objects, schedules: j.schedules, outbox: Map::empty() }, r), abs_run(a, acts, rt))
        &&& abs_responses(a, acts, rt) == Seq::<AbsResponse>::empty()
        &&& inside_obj(full(new), in_origin(o))
    }),
{
    let f = in_origin(o);
    let g = sched_in(st);
    let b = glue(j, r);
    let cs = j.schedules.union_prefer_right(r.schedules);
    let c = j.schedules[sid];
    let occ = AOccurrence { at: c.next_run_at, promise_id: pid };
    let occs: Seq<AOccurrence> = seq![occ];
    assert(occs.len() == 1 && occs[0] == occ);
    lemma_glue_has_sched(j, r, g, sid);
    assert(b.schedules.contains_key(sid) && b.schedules[sid] == c);
    assert(canonical(sid)) by {
        assert(c.id == sid && canonical_schedule(c));
    }
    lemma_inv_basics(t as nat, j);
    assert(c.promise_timeout <= kernel::MAX_TIME);
    assert(canonical_occurrences(occs));
    assert(occurrences_due(c, occs, t));
    // the occurrence fired, on the bucket and on the document
    lemma_fire_fold_sim(b, a, sid, c, occs, t, rt, 1);
    let fa = fire_actions(b, sid, c, occs, t, 1);
    let a1 = internal_run(a, fa, t, rt);
    lemma_inv_shape(t as nat, j, o);
    assert(occs_inside(occs, f));
    lemma_fire_fold_local(j, r, cs, f, c, occs, 1, t as nat);
    let f1 = kint::fire_fold(t as nat, j, c, occs, 1);
    let gg = gobj(f1, r, cs);
    assert(kint::fire_fold(t as nat, b, c, occs, 1) == gg);
    assert(doc_related(gg, a1));
    // the fired state is the fold with the row advanced
    let fired = kint::spec_fire(j, sid, occs, next, t as nat);
    assert(fired == KState { schedules: f1.schedules.insert(sid, ASchedule { last_run_at: Some(occ.at), next_run_at: next, ..c }), ..f1 });
    assert(fired.objects == f1.objects);
    // the sweep on the fired state is the sweep of the fold's objects
    let e = KState { objects: Map::empty(), schedules: Map::empty(), outbox: Map::empty() };
    assert(gobj(f1, e, fired.schedules).objects =~= fired.objects);
    assert(gobj(f1, e, fired.schedules) == fired);
    assert forall|i: int| 0 <= i < ids.len() implies f1.objects.contains_key(#[trigger] ids[i]) by {
        assert(fired.objects.contains_key(ids[i]));
    }
    assert(ids_inside(ids, f)) by {
        assert forall|i: int| 0 <= i < ids.len() implies f(#[trigger] ids[i]) by {
            assert(f1.objects.contains_key(ids[i]));
        }
    }
    lemma_single_pass_local(f1, e, fired.schedules, f, ids, t as nat, rt as nat);
    let f2 = ksteps::executable_single_pass(f1, ids, t as nat, rt as nat);
    let swept = ksteps::executable_single_pass(fired, ids, t as nat, rt as nat);
    assert(swept == gobj(f2, e, fired.schedules));
    assert(swept.objects =~= f2.objects);
    // the sweep on the bucket
    lemma_single_pass_local(f1, r, cs, f, ids, t as nat, rt as nat);
    assert(ksteps::executable_single_pass(gg, ids, t as nat, rt as nat) == gobj(f2, r, cs));
    assert forall|i: int| 0 <= i < ids.len() implies gg.objects.contains_key(#[trigger] ids[i]) by {
        assert(f1.objects.contains_key(ids[i]));
    }
    lemma_related_canonical(gg, a1, ids);
    assert(not_self(gg)) by {
        assert forall|id: Chars| #[trigger] gg.objects.contains_key(id) implies !gg.objects[id].callbacks.contains(id) by {
            if r.objects.contains_key(id) {
                assert(gg.objects[id] == r.objects[id]);
            } else {
                assert(f1.objects.contains_key(id) && gg.objects[id] == f1.objects[id]);
            }
        }
    }
    let sa = sweep_actions(gg, ids, t, rt);
    lemma_sweep_sim(gg, a1, ids, t, rt);
    let a2 = internal_run(a1, sa, t, rt);
    assert(doc_related(gobj(f2, r, cs), a2));
    // the run, assembled
    let acts = fire_step_actions(j, r, sid, pid, ids, t, rt);
    assert(acts == lift(fa, t) + lift(sa, t));
    lemma_lift_run(a, fa, t, rt);
    lemma_lift_run(a1, sa, t, rt);
    lemma_abs_run_app(a, lift(fa, t), lift(sa, t), rt);
    assert(abs_run(a, acts, rt) == a2);
    assert(abs_responses(a, acts, rt) =~= Seq::<AbsResponse>::empty());
    // the written objects beside the schedule's rows and the rest
    let new = objects_only(swept);
    let target = glue(KState { objects: new.objects, schedules: j.schedules, outbox: Map::empty() }, r);
    assert(target.objects == gobj(f2, r, cs).objects);
    assert(target.schedules == cs);
    lemma_related_outbox(gobj(f2, r, cs), target, a2);
    assert(inside_obj(full(new), f));
}

/// The Abstract action a schedule's advance is.
pub open spec fn advance_step_actions(sid: Chars, last: AOccurrence, next: u64, t: u64) -> Seq<AbsAction> {
    seq![AbsAction::Internal(AbsInternal::ScheduleAdvance(advance_req(sid, last, next)), t)]
}

/// The schedule's row advanced past an occurrence whose promise is in the
/// bucket: the fire's second half.
pub proof fn lemma_advance_step(l: KState, r: KState, a: AState, st: Origin, sid: Chars, last: AOccurrence, next: u64, t: u64, rt: u64)
    requires
        doc_related(glue(l, r), a),
        inside_sch(l, sched_in(st)), outside_sch(r, sched_in(st)),
        sched_target(sid) == st,
        l.schedules.contains_key(sid),
        l.schedules[sid].next_run_at <= last.at,
        last.at <= t,
        last.at < next,
        glue(l, r).objects.contains_key(last.promise_id),
    ensures ({
        let c = l.schedules[sid];
        let c2 = ASchedule { last_run_at: Some(last.at), next_run_at: next, ..c };
        let acts = advance_step_actions(sid, last, next, t);
        &&& doc_related(glue(KState { schedules: l.schedules.insert(sid, c2), ..l }, r), abs_run(a, acts, rt))
        &&& abs_responses(a, acts, rt) == Seq::<AbsResponse>::empty()
    }),
{
    let g = sched_in(st);
    let b = glue(l, r);
    let c = l.schedules[sid];
    lemma_glue_has_sched(l, r, g, sid);
    assert(b.schedules.contains_key(sid) && b.schedules[sid] == c);
    assert(canonical(sid)) by {
        assert(c.id == sid && canonical_schedule(c));
    }
    assert(canonical(last.promise_id)) by {
        let p = b.objects[last.promise_id];
        assert(p.id == last.promise_id && canonical_promise(p));
    }
    lemma_advance_sim(b, a, sid, last, next, t, rt);
    let c2 = ASchedule { last_run_at: Some(last.at), next_run_at: next, ..c };
    lemma_glue_insert_sched(l, r, g, sid, c2);
    let act = AbsInternal::ScheduleAdvance(advance_req(sid, last, next));
    let acts = advance_step_actions(sid, last, next, t);
    assert(acts == lift(seq![act], t)) by {
        assert(lift(seq![act], t) =~= acts);
    }
    lemma_lift_run(a, seq![act], t, rt);
    lemma_internal_run_one(a, act, t, rt);
}

} // verus!
