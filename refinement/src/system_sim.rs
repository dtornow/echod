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
use echod_kernel::node::*;
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

// ---------------------------------------------------------------------------
// The refinement invariant
// ---------------------------------------------------------------------------

/// The observable: each request served, with its answer, as the Abstract's.
pub open spec fn observed(log: Seq<Served>) -> Seq<AbsResponse> {
    log.map_values(|sv: Served| response(sv.req, sv.resp))
}

/// `acts` explains the cluster: the Abstract's run by `acts` from its
/// initial state ends related to the bucket and answers exactly the log.
pub open spec fn explains(s: Cluster, acts: Seq<AbsAction>) -> bool {
    &&& doc_related(bucket(s), abs_run(abstract_init(), acts, s.rt as u64))
    &&& abs_responses(abstract_init(), acts, s.rt as u64) == observed(s.log)
}

/// Some Abstract run explains the cluster.
pub open spec fn refines(s: Cluster) -> bool {
    exists|acts: Seq<AbsAction>| explains(s, acts)
}

/// A request in flight: the kernel's three functions on what was loaded,
/// with the doors its handler needs. `m` is the swept document.
pub open spec fn request_shape(rt: nat, o: Origin, x: Flight, req: ARequest, m: Doc) -> bool {
    &&& x.then is None
    &&& computed_request(x.loaded, req, x.t, rt, m, x.new)
    &&& kprops::inv(x.t, full(m))
    &&& doc_headroom(full(m))
    &&& request_doors(req, x.t as u64)
    &&& request_inside(req, in_origin(o), sched_in(o))
}

/// The fire's second half, as a flight on the schedule's document: the
/// row `sid` advanced past the occurrence the first half fired, to `next`.
pub open spec fn advanced(o: Origin, x: Flight, sid: Chars, next: u64) -> bool {
    let c = x.loaded.schedules[sid];
    &&& o == sched_target(sid)
    &&& x.loaded.objects == Map::<Chars, APromise>::empty()
    &&& x.loaded.schedules.contains_key(sid)
    &&& c.next_run_at <= x.t
    &&& c.next_run_at < next
    &&& x.new == Doc { objects: Map::empty(), schedules: x.loaded.schedules.insert(sid, ASchedule { last_run_at: Some(c.next_run_at), next_run_at: next, ..c }) }
}

pub open spec fn second_half(o: Origin, x: Flight) -> bool {
    exists|sid: Chars, next: u64| advanced(o, x, sid, next)
}

/// A fire in flight: the kernel's functions on the origin's objects and the
/// schedule's row as read, the second half decided with it.
pub open spec fn fire_shape(rt: nat, o: Origin, x: Flight, sid: Chars, pid: Chars, next: u64) -> bool {
    match x.then {
        None => false,
        Some(p) => {
            let c = p.loaded.schedules[sid];
            let fired = kint::spec_fire(joint(x.loaded, p.loaded), sid, seq![AOccurrence { at: c.next_run_at, promise_id: pid }], next, x.t);
            &&& p.target == sched_target(sid)
            &&& p.pid == pid
            &&& origin(pid) == o
            &&& canonical(pid)
            &&& p.loaded.schedules.contains_key(sid)
            &&& c.next_run_at <= x.t
            &&& c.next_run_at < next
            &&& computed_fire(fired, x.t, rt, x.new)
            &&& p.new == Doc { objects: Map::empty(), schedules: p.loaded.schedules.insert(sid, ASchedule { last_run_at: Some(c.next_run_at), next_run_at: next, ..c }) }
        }
    }
}

/// What a flight is: the kernel's functions for its work on what it loaded.
pub open spec fn flight_shape(rt: nat, o: Origin, x: Flight) -> bool {
    match x.work {
        Work::Request(req, m) => request_shape(rt, o, x, req, m),
        Work::Sweep(_) => x.then is None && (computed_sweep(x.loaded, x.t, rt, x.new) || second_half(o, x)),
        Work::Fire(_, sid, pid, next, _) => fire_shape(rt, o, x, sid, pid, next),
    }
}

pub open spec fn flights_shaped(s: Cluster) -> bool {
    forall|i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> flight_shape(s.rt, o, s.nodes[i].txns[o])
}

/// A fire's schedule document is as the fire read it until the promise's
/// commit. A hypothesis on behaviours: the fleet commits the promise
/// without re-reading the schedule.
pub open spec fn schedule_held(s: Cluster) -> bool {
    forall|i: Id, o: Origin| s.nodes.contains_key(i) && #[trigger] s.nodes[i].txns.contains_key(o) ==> match s.nodes[i].txns[o].then {
        Some(p) => !(s.nodes[i].txns[o].phase is Process) ==> s.store.doc(p.target) == p.loaded,
        None => true,
    }
}

/// The doors on a step: the bucket within the wire's bounds and the fire's
/// schedule held; a prepared request's doors, its swept document within
/// the bounds, a heartbeat's refs of one origin; a fire's promise id well
/// formed.
pub open spec fn admitted(s: Cluster, st: Step) -> bool {
    &&& store_headroom(s)
    &&& schedule_held(s)
    &&& match st {
        Step::Prepare(i, o, t, work, new, did, deadline) => match work {
            Work::Request(req, m) => {
                &&& request_doors(req, t as u64)
                &&& doc_headroom(full(m))
                &&& match req { ARequest::TaskHeartbeat(q) => refs_inside(q.tasks, in_origin(o)), _ => true }
            }
            Work::Fire(_, _, pid, _, _) => canonical(pid),
            Work::Sweep(_) => true,
        },
        _ => true,
    }
}

/// A step of the fleet within the doors.
pub open spec fn next_admitted() -> spec_fn(Cluster, Cluster) -> bool {
    |s: Cluster, s2: Cluster| exists|st: Step| #[trigger] next_step(s, s2, st) && admitted(s, st)
}

/// The refinement's part of the invariant.
pub open spec fn ref_state(s: Cluster) -> bool {
    &&& partitioned(s)
    &&& flights_shaped(s)
    &&& refines(s)
}

pub open spec fn inv_ref() -> spec_fn(Cluster) -> bool {
    |s: Cluster| {
        &&& sys::inv()(s)
        &&& s.rt <= kernel::MAX_TIME
        &&& ref_state(s)
    }
}

// ---------------------------------------------------------------------------
// Frames
// ---------------------------------------------------------------------------

/// A step that leaves the bucket and the log alone is explained as before.
pub proof fn lemma_stutter(s: Cluster, s2: Cluster)
    requires refines(s), bucket(s2) == bucket(s), s2.log == s.log, s2.rt == s.rt,
    ensures refines(s2),
{
    let acts = choose|acts: Seq<AbsAction>| explains(s, acts);
    assert(explains(s2, acts));
}

/// A step that leaves the documents alone.
pub proof fn lemma_stutter_docs(s: Cluster, s2: Cluster)
    requires refines(s), partitioned(s), s2.store.docs == s.store.docs, s2.log == s.log, s2.rt == s.rt,
    ensures refines(s2), partitioned(s2),
{
    lemma_bucket_same(s, s2);
    lemma_stutter(s, s2);
}

/// A flight's shape is of its work, loaded and new documents, instant and
/// second half: the commit's progress does not touch it.
pub proof fn lemma_shape_same(rt: nat, o: Origin, x: Flight, x2: Flight)
    requires
        flight_shape(rt, o, x),
        x2.work == x.work, x2.then == x.then, x2.loaded == x.loaded, x2.new == x.new, x2.t == x.t,
    ensures flight_shape(rt, o, x2),
{
    match x.work {
        Work::Request(req, m) => {}
        Work::Sweep(_) => {
            if second_half(o, x) {
                let (sid, next) = choose|sid: Chars, next: u64| advanced(o, x, sid, next);
                assert(advanced(o, x2, sid, next));
            }
        }
        Work::Fire(_, sid, pid, next, _) => {}
    }
}

/// Flights keep their shape when only node `i`'s change, and those are shaped.
pub proof fn lemma_shapes_frame(s: Cluster, s2: Cluster, i: Id)
    requires
        flights_shaped(s), s2.rt == s.rt,
        forall|j: Id| #[trigger] s2.nodes.contains_key(j) && j != i ==> s.nodes.contains_key(j) && s2.nodes[j].txns == s.nodes[j].txns,
        s2.nodes.contains_key(i) ==> forall|o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) ==> flight_shape(s.rt, o, s2.nodes[i].txns[o]),
    ensures flights_shaped(s2),
{
    assert forall|j: Id, o: Origin| s2.nodes.contains_key(j) && #[trigger] s2.nodes[j].txns.contains_key(o) implies flight_shape(s2.rt, o, s2.nodes[j].txns[o]) by {
        if j != i {
            assert(s.nodes[j].txns.contains_key(o));
        }
    }
}

/// Node `i` keeps its flights, or drops one: the shapes stay.
pub proof fn lemma_shapes_kept(s: Cluster, s2: Cluster, i: Id)
    requires
        flights_shaped(s), s2.rt == s.rt, s.nodes.contains_key(i),
        forall|j: Id| #[trigger] s2.nodes.contains_key(j) && j != i ==> s.nodes.contains_key(j) && s2.nodes[j].txns == s.nodes[j].txns,
        s2.nodes.contains_key(i) ==> forall|o: Origin| #[trigger] s2.nodes[i].txns.contains_key(o) ==> s.nodes[i].txns.contains_key(o) && s2.nodes[i].txns[o] == s.nodes[i].txns[o],
    ensures flights_shaped(s2),
{
    lemma_shapes_frame(s, s2, i);
}

/// The second half continued from a shaped fire is shaped.
pub proof fn lemma_continued_shape(s: Cluster, rt: nat, o: Origin, x: Flight, core: ANode)
    requires
        flight_shape(rt, o, x),
        x.then is Some,
        shaped(x.then.unwrap().target, x.then.unwrap().loaded),
    ensures flight_shape(rt, x.then.unwrap().target, continued(s, core, x.then.unwrap(), x.t)),
{
    let p = x.then.unwrap();
    let y = continued(s, core, p, x.t);
    match x.work {
        Work::Request(req, m) => {}
        Work::Sweep(_) => {}
        Work::Fire(_, sid, pid, next, _) => {
            assert(is_sched(p.target)) by { lemma_sched_target_is_sched(sid); }
            assert(advanced(p.target, y, sid, next));
        }
    }
}

// ---------------------------------------------------------------------------
// The steps that move only a node, or a timer
// ---------------------------------------------------------------------------

pub proof fn lemma_ref_tick(s: Cluster, s2: Cluster, i: Id, d: nat)
    requires ref_state(s), tick(s, i, d) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    lemma_shapes_kept(s, s2, i);
}

pub proof fn lemma_ref_join(s: Cluster, s2: Cluster, i: Id, c: nat)
    requires ref_state(s), join(s, i, c) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    lemma_shapes_frame(s, s2, i);
}

pub proof fn lemma_ref_crash(s: Cluster, s2: Cluster, i: Id)
    requires ref_state(s), crash(s, i) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    lemma_shapes_kept(s, s2, i);
}

pub proof fn lemma_ref_forget(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires ref_state(s), forget(s, i, o) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    lemma_shapes_kept(s, s2, i);
}

pub proof fn lemma_ref_arm(s: Cluster, s2: Cluster, i: Id, o: Origin, k: AKey)
    requires ref_state(s), arm(s, i, o, k) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    let n = s.nodes[i];
    let x = n.txns[o];
    let x2 = s2.nodes[i].txns[o];
    assert(flight_shape(s.rt, o, x));
    lemma_shape_same(s.rt, o, x, x2);
    assert forall|q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies flight_shape(s.rt, q, s2.nodes[i].txns[q]) by {
        if q != o {
            assert(s.nodes[i].txns.contains_key(q));
        }
    }
    lemma_shapes_frame(s, s2, i);
}

pub proof fn lemma_ref_give_up(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires ref_state(s), s.nodes.contains_key(i), s2 == give_up(s, i, o),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    lemma_shapes_kept(s, s2, i);
}

pub proof fn lemma_ref_commit_fail(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires ref_state(s), commit_fail(s, i, o) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    lemma_shapes_kept(s, s2, i);
}

pub proof fn lemma_ref_collect_fail(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires ref_state(s), collect_fail(s, i, o) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    lemma_shapes_kept(s, s2, i);
}

pub proof fn lemma_ref_disarm(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires ref_state(s), disarm(s, i, o) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt, s2.nodes == s.nodes,
{
    lemma_stutter_docs(s, s2);
}

/// The second half of a flight on `o` at node `i`, if any, is shaped for
/// its document: what `finish` and `done` need of the system invariant.
pub open spec fn pending_shaped(s: Cluster, i: Id, o: Origin) -> bool {
    match s.nodes[i].txns[o].then {
        Some(p) => shaped(p.target, p.loaded),
        None => true,
    }
}

pub proof fn lemma_pending_shaped(s: Cluster, i: Id, o: Origin)
    requires sys::inv()(s), s.nodes.contains_key(i), s.nodes[i].txns.contains_key(o),
    ensures pending_shaped(s, i, o),
{
    sys::disassemble(s);
    assert(sys::inv_txn(s, i, o));
}

/// The node's flights once the one on `o` is done: those it had, less that
/// one, plus the second half it continues into.
pub proof fn lemma_ref_after(s: Cluster, s2: Cluster, i: Id, o: Origin, core: ANode)
    requires
        ref_state(s), s.nodes.contains_key(i), s.nodes[i].txns.contains_key(o), pending_shaped(s, i, o),
        s2.rt == s.rt, s2.nodes.contains_key(i),
        s2.nodes[i].txns == after(s, core, s.nodes[i], o),
        forall|j: Id| #[trigger] s2.nodes.contains_key(j) && j != i ==> s.nodes.contains_key(j) && s2.nodes[j].txns == s.nodes[j].txns,
    ensures flights_shaped(s2),
{
    let n = s.nodes[i];
    let x = n.txns[o];
    assert(flight_shape(s.rt, o, x));
    match x.then {
        Some(p) => {
            lemma_continued_shape(s, s.rt, o, x, core);
            assert forall|q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies flight_shape(s.rt, q, s2.nodes[i].txns[q]) by {
                if q != p.target {
                    assert(n.txns.contains_key(q));
                }
            }
        }
        None => {
            assert forall|q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies flight_shape(s.rt, q, s2.nodes[i].txns[q]) by {
                assert(n.txns.contains_key(q));
            }
        }
    }
    lemma_shapes_frame(s, s2, i);
}

pub proof fn lemma_ref_finish(s: Cluster, s2: Cluster, i: Id, o: Origin, deleted: bool)
    requires ref_state(s), pending_shaped(s, i, o), finish(s, i, o, deleted) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    let n = s.nodes[i];
    let x = n.txns[o];
    let core1 = spec_finish(n.core, x.c, x.cur.unwrap());
    let core2 = match x.c.fired {
        Some(k) => if deleted { spec_collected(core1, o, k) } else { core1 },
        None => core1,
    };
    assert(s2.nodes[i].txns == after(s, core2, n, o));
    lemma_ref_after(s, s2, i, o, core2);
}

pub proof fn lemma_ref_done(s: Cluster, s2: Cluster, i: Id, o: Origin)
    requires ref_state(s), pending_shaped(s, i, o), done(s, i, o) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_stutter_docs(s, s2);
    let n = s.nodes[i];
    assert(s2.nodes[i].txns == after(s, n.core, n, o));
    lemma_ref_after(s, s2, i, o, n.core);
}

/// The document a collecting rewrite puts back is the one in the bucket.
pub proof fn lemma_collect_rewrites(s: Cluster, i: Id, o: Origin)
    requires
        sys::inv()(s), s.nodes.contains_key(i), s.nodes[i].txns.contains_key(o),
        s.nodes[i].txns[o].phase is Prepare, sys::live(s, o, s.nodes[i].txns[o]),
    ensures s.store.doc(o) == s.nodes[i].txns[o].loaded,
{
    sys::disassemble(s);
    assert(sys::inv_txn(s, i, o));
}

pub proof fn lemma_ref_collect(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires sys::inv()(s), ref_state(s), collect(s, i, o, e) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_collect_rewrites(s, i, o);
    lemma_rewritten(s, s2, o);
    lemma_stutter(s, s2);
    lemma_shapes_kept(s, s2, i);
}

pub proof fn lemma_ref_collect_unknown(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>, landed: bool)
    requires sys::inv()(s), ref_state(s), collect_unknown(s, i, o, e, landed) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    if landed {
        lemma_collect_rewrites(s, i, o);
        lemma_rewritten(s, s2, o);
        lemma_stutter(s, s2);
    } else {
        lemma_stutter_docs(s, s2);
    }
    lemma_shapes_kept(s, s2, i);
}

// ---------------------------------------------------------------------------
// A commit, explained: the flight's kernel step on its document is an
// Abstract run from the run that explains the bucket
// ---------------------------------------------------------------------------

/// The Abstract run that explains `s` extended by one more: the bucket
/// after is related to where the extension ends, and the extension answers
/// what the log gained.
pub proof fn lemma_explains_step(s: Cluster, s2: Cluster, acts: Seq<AbsAction>, racts: Seq<AbsAction>, resp: Seq<AbsResponse>)
    requires
        explains(s, acts), s2.rt == s.rt,
        doc_related(bucket(s2), abs_run(abs_run(abstract_init(), acts, s.rt as u64), racts, s.rt as u64)),
        abs_responses(abs_run(abstract_init(), acts, s.rt as u64), racts, s.rt as u64) == resp,
        observed(s2.log) == observed(s.log) + resp,
    ensures explains(s2, acts + racts), refines(s2),
{
    lemma_abs_run_app(abstract_init(), acts, racts, s.rt as u64);
    assert(explains(s2, acts + racts));
}

pub proof fn lemma_observed_same(log: Seq<Served>)
    ensures observed(log) == observed(log) + Seq::<AbsResponse>::empty(),
{
    assert(observed(log) =~= observed(log) + Seq::<AbsResponse>::empty());
}

pub proof fn lemma_observed_push(log: Seq<Served>, sv: Served)
    ensures observed(log.push(sv)) == observed(log) + seq![response(sv.req, sv.resp)],
{
    assert(observed(log.push(sv)) =~= observed(log) + seq![response(sv.req, sv.resp)]);
}

/// `racts` explains a request's flight `x` on `o` from the run `a`: the
/// Abstract ends related to the written document beside the rest of the
/// bucket, and answers the request's response alone.
pub open spec fn request_explains(s: Cluster, o: Origin, x: Flight, req: ARequest, m: Doc, a: AState, racts: Seq<AbsAction>) -> bool {
    let r = rest(s, in_origin(o), sched_in(o));
    let rt = s.rt as u64;
    &&& doc_related(glue(full(x.new), r), abs_run(a, racts, rt))
    &&& abs_responses(a, racts, rt) == seq![response(req, kext::spec_handle(full(m), req, x.t).1)]
}

/// A request's flight, as read from the bucket, is an Abstract run.
pub proof fn lemma_request_run(s: Cluster, o: Origin, x: Flight, req: ARequest, m: Doc, a: AState)
    requires
        sys::inv()(s), partitioned(s), store_headroom(s), s.rt <= kernel::MAX_TIME,
        request_shape(s.rt, o, x, req, m),
        s.store.doc(o) == x.loaded,
        x.t <= kernel::MAX_TIME,
        kprops::inv(x.t, full(x.loaded)),
        doc_related(bucket(s), a),
    ensures
        exists|racts: Seq<AbsAction>| request_explains(s, o, x, req, m, a, racts),
        doc_inside(x.new, o),
{
    let r = rest(s, in_origin(o), sched_in(o));
    let k = full(x.loaded);
    let t = x.t as u64;
    let rt = s.rt as u64;
    assert(t as nat == x.t);
    assert(rt as nat == s.rt);
    lemma_split_doc(s, o);
    lemma_rest_basics(s, in_origin(o), sched_in(o));
    let (ids1, ids2) = choose|ids1: Seq<Chars>, ids2: Seq<Chars>| {
        &&& #[trigger] object_order(k, ids1)
        &&& m == strip(ksteps::executable_single_pass(k, ids1, x.t, s.rt))
        &&& #[trigger] object_order(kext::spec_handle(full(m), req, x.t).0, ids2)
        &&& x.new == strip(ksteps::executable_single_pass(kext::spec_handle(full(m), req, x.t).0, ids2, x.t, s.rt))
    };
    lemma_request_step(k, r, a, o, ids1, m, req, ids2, t, rt);
    let racts = request_step_actions(k, r, ids1, m, req, ids2, t, rt);
    assert(request_explains(s, o, x, req, m, a, racts));
}

/// The commit of a request's flight: the document written, the response
/// logged.
pub proof fn lemma_commit_request(s: Cluster, s2: Cluster, o: Origin, x: Flight, req: ARequest, m: Doc)
    requires
        sys::inv()(s), partitioned(s), refines(s), store_headroom(s), s.rt <= kernel::MAX_TIME,
        request_shape(s.rt, o, x, req, m),
        x.work == Work::Request(req, m),
        s.store.doc(o) == x.loaded,
        x.t <= kernel::MAX_TIME,
        kprops::inv(x.t, full(x.loaded)),
        s2.store.docs == s.store.docs.insert(o, x.new),
        s2.log == answered(s, o, x),
        s2.rt == s.rt,
    ensures partitioned(s2), refines(s2),
{
    let rt = s.rt as u64;
    let acts = choose|acts: Seq<AbsAction>| explains(s, acts);
    let a = abs_run(abstract_init(), acts, rt);
    lemma_request_run(s, o, x, req, m, a);
    let racts = choose|racts: Seq<AbsAction>| request_explains(s, o, x, req, m, a, racts);
    lemma_written_doc(s, s2, o, x.new);
    let res = kext::spec_handle(full(m), req, x.t).1;
    lemma_observed_push(s.log, Served { origin: o, at: x.t, req, resp: res });
    lemma_explains_step(s, s2, acts, racts, seq![response(req, res)]);
}

/// The commit of a sweep's flight: the document written, nothing logged.
pub proof fn lemma_commit_sweep(s: Cluster, s2: Cluster, o: Origin, x: Flight)
    requires
        sys::inv()(s), partitioned(s), refines(s), store_headroom(s), s.rt <= kernel::MAX_TIME,
        computed_sweep(x.loaded, x.t, s.rt, x.new),
        s.store.doc(o) == x.loaded,
        x.t <= kernel::MAX_TIME,
        kprops::inv(x.t, full(x.loaded)),
        s2.store.docs == s.store.docs.insert(o, x.new),
        s2.log == s.log,
        s2.rt == s.rt,
    ensures partitioned(s2), refines(s2),
{
    let rt = s.rt as u64;
    let t = x.t as u64;
    assert(t as nat == x.t);
    assert(rt as nat == s.rt);
    let acts = choose|acts: Seq<AbsAction>| explains(s, acts);
    let a = abs_run(abstract_init(), acts, rt);
    let r = rest(s, in_origin(o), sched_in(o));
    let k = full(x.loaded);
    lemma_split_doc(s, o);
    lemma_rest_basics(s, in_origin(o), sched_in(o));
    lemma_inv_shape(x.t, k, o);
    let ids = choose|ids: Seq<Chars>| #[trigger] object_order(k, ids) && x.new == strip(ksteps::executable_single_pass(k, ids, x.t, s.rt));
    lemma_sweep_step(k, r, a, in_origin(o), ids, t, rt);
    let k2 = ksteps::executable_single_pass(k, ids, x.t, s.rt);
    assert(doc_inside(x.new, o)) by {
        assert(full(x.new).objects == k2.objects);
        assert(full(x.new).schedules == k.schedules);
    }
    lemma_written_doc(s, s2, o, x.new);
    lemma_observed_same(s.log);
    lemma_explains_step(s, s2, acts, sweep_step_actions(k, r, ids, t, rt), Seq::empty());
}

/// The commit of a fire's second half: the schedule's row advanced past
/// the occurrence whose promise the first half committed.
pub proof fn lemma_commit_advance(s: Cluster, s2: Cluster, o: Origin, x: Flight, sid: Chars, next: u64)
    requires
        sys::inv()(s), partitioned(s), refines(s), s.rt <= kernel::MAX_TIME,
        advanced(o, x, sid, next),
        sys::runs_have_promises(s, x.new),
        s.store.doc(o) == x.loaded,
        x.t <= kernel::MAX_TIME,
        s2.store.docs == s.store.docs.insert(o, x.new),
        s2.log == s.log,
        s2.rt == s.rt,
    ensures partitioned(s2), refines(s2),
{
    let rt = s.rt as u64;
    let t = x.t as u64;
    assert(t as nat == x.t);
    assert(rt as nat == s.rt);
    let acts = choose|acts: Seq<AbsAction>| explains(s, acts);
    let a = abs_run(abstract_init(), acts, rt);
    let r = rest(s, in_origin(o), sched_in(o));
    let l = full(x.loaded);
    lemma_split_doc(s, o);
    let c = x.loaded.schedules[sid];
    let c2 = ASchedule { last_run_at: Some(c.next_run_at), next_run_at: next, ..c };
    let pid = expand(c.promise_id, sid, c.next_run_at as nat);
    // the occurrence's promise is in the bucket: the row's last run has it
    assert(x.new.schedules.contains_key(sid) && x.new.schedules[sid] == c2);
    assert(sys::has_promise(s, c2, sid, c.next_run_at as nat));
    lemma_bucket_has(s);
    assert(s.store.doc(origin(pid)) == s.store.docs[origin(pid)]);
    assert(bucket_objects(s).contains_key(pid));
    let last = AOccurrence { at: c.next_run_at, promise_id: pid };
    lemma_advance_step(l, r, a, o, sid, last, next, t, rt);
    assert(full(x.new) == KState { schedules: l.schedules.insert(sid, c2), ..l });
    assert(doc_inside(x.new, o)) by {
        assert forall|q: Chars| #[trigger] full(x.new).schedules.contains_key(q) implies sched_in(o)(q) by {
            if q != sid {
                assert(l.schedules.contains_key(q));
            }
        }
    }
    lemma_written_doc(s, s2, o, x.new);
    lemma_observed_same(s.log);
    lemma_explains_step(s, s2, acts, advance_step_actions(sid, last, next, t), Seq::empty());
}

/// The commit of a fire's first half: the origin's objects written with the
/// occurrence's promise, beside the schedule's document as the fire read it.
pub proof fn lemma_commit_fire(s: Cluster, s2: Cluster, o: Origin, x: Flight, sid: Chars, pid: Chars, next: u64)
    requires
        sys::inv()(s), partitioned(s), refines(s), store_headroom(s), s.rt <= kernel::MAX_TIME,
        fire_shape(s.rt, o, x, sid, pid, next),
        s.store.doc(o) == x.loaded,
        s.store.doc(x.then.unwrap().target) == x.then.unwrap().loaded,
        x.t <= kernel::MAX_TIME,
        kprops::inv(x.t, full(x.loaded)),
        kprops::inv(x.t, full(x.then.unwrap().loaded)),
        shaped(o, x.loaded), shaped(o, x.new),
        shaped(x.then.unwrap().target, x.then.unwrap().loaded),
        s2.store.docs == s.store.docs.insert(o, x.new),
        s2.log == s.log,
        s2.rt == s.rt,
    ensures partitioned(s2), refines(s2),
{
    let rt = s.rt as u64;
    let t = x.t as u64;
    assert(t as nat == x.t);
    assert(rt as nat == s.rt);
    let acts = choose|acts: Seq<AbsAction>| explains(s, acts);
    let a = abs_run(abstract_init(), acts, rt);
    let p = x.then.unwrap();
    let st = p.target;
    sys::lemma_origin_not_sched(pid);
    lemma_sched_target_is_sched(sid);
    lemma_split_joint(s, o, st);
    let j = joint(x.loaded, p.loaded);
    let r = rest(s, in_origin(o), sched_in(st));
    ksteps::lemma_inv_joint(x.t, x.loaded, p.loaded);
    lemma_rest_basics(s, in_origin(o), sched_in(st));
    let c = p.loaded.schedules[sid];
    let occ = AOccurrence { at: c.next_run_at, promise_id: pid };
    let fired = kint::spec_fire(j, sid, seq![occ], next, x.t);
    let ids = choose|ids: Seq<Chars>| #[trigger] object_order(fired, ids) && x.new == objects_only(ksteps::executable_single_pass(fired, ids, x.t, s.rt));
    assert(j.schedules[sid] == c);
    lemma_fire_step(j, r, a, o, st, sid, pid, next, ids, t, rt);
    assert(joint(x.new, p.loaded) == KState { objects: x.new.objects, schedules: j.schedules, outbox: Map::empty() });
    assert(doc_inside(x.new, o)) by {
        assert(full(x.new).schedules == Map::<Chars, ASchedule>::empty());
    }
    lemma_written_joint(s, s2, o, st, x.new);
    lemma_observed_same(s.log);
    lemma_explains_step(s, s2, acts, fire_step_actions(j, r, sid, pid, ids, t, rt), Seq::empty());
}

/// The commit: the flight's document written at a new version, its answer
/// logged. Its shape says which kernel step it is; the bucket's relation
/// and the system invariant say the step is from the bucket.
pub proof fn lemma_ref_commit(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>)
    requires
        sys::inv()(s), s.rt <= kernel::MAX_TIME, ref_state(s), store_headroom(s), schedule_held(s),
        commit(s, i, o, e) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    let n = s.nodes[i];
    let x = n.txns[o];
    sys::disassemble(s);
    assert(sys::inv_txn(s, i, o));
    assert(!(x.phase is Process));
    assert(sys::live(s, o, x));
    assert(s.store.doc(o) == x.loaded);
    assert(flight_shape(s.rt, o, x));
    // the flights: the one on `o` moves to its write, the rest stay
    let x2 = s2.nodes[i].txns[o];
    lemma_shape_same(s.rt, o, x, x2);
    assert forall|q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies flight_shape(s.rt, q, s2.nodes[i].txns[q]) by {
        if q != o {
            assert(n.txns.contains_key(q));
        }
    }
    lemma_shapes_frame(s, s2, i);
    // the bucket and the log
    match x.work {
        Work::Request(req, m) => {
            lemma_commit_request(s, s2, o, x, req, m);
        }
        Work::Sweep(_) => {
            if second_half(o, x) {
                let (sid, next) = choose|sid: Chars, next: u64| advanced(o, x, sid, next);
                lemma_commit_advance(s, s2, o, x, sid, next);
            } else {
                lemma_commit_sweep(s, s2, o, x);
            }
        }
        Work::Fire(_, sid, pid, next, _) => {
            let p = x.then.unwrap();
            assert(sys::inv_pending(s, o, x, p));
            assert(s.store.doc(p.target) == p.loaded);
            lemma_commit_fire(s, s2, o, x, sid, pid, next);
        }
    }
}

// ---------------------------------------------------------------------------
// The read: a flight begins, shaped; a request that changed nothing is
// answered here
// ---------------------------------------------------------------------------

/// The flight `prepare` puts up is shaped: what the node computes is the
/// kernel's functions on what it loaded, with the doors the step admits.
pub proof fn lemma_prepared_shape(s: Cluster, s2: Cluster, i: Id, o: Origin, t: nat, work: Work, new: Doc, did: bool, deadline: Option<nat>)
    requires
        sys::inv()(s2),
        admitted(s, Step::Prepare(i, o, t, work, new, did, deadline)),
        prepare(s, i, o, t, work, new, did, deadline) == Some(s2),
    ensures flight_shape(s.rt, o, s2.nodes[i].txns[o]),
{
    let loaded = s.store.doc(o);
    let x = s2.nodes[i].txns[o];
    sys::disassemble(s2);
    assert(s2.nodes.contains_key(i) && s2.nodes[i].txns.contains_key(o));
    assert(sys::inv_txn(s2, i, o));
    assert(x.loaded == loaded && x.new == new && x.t == t && x.work == work);
    match work {
        Work::Request(req, m) => {
            let d = choose|d: bool| #[trigger] ksteps::swept_by(t, full(loaded), full(m), d);
            ksteps::lemma_reach_inv(t, full(loaded), full(m));
            lemma_target_inside(req, o);
            assert(request_shape(s.rt, o, x, req, m));
        }
        Work::Sweep(k) => {
            assert(x.then is None);
            assert(computed_sweep(x.loaded, x.t, s.rt, x.new));
        }
        Work::Fire(k, sid, pid, next, deadline_s) => {
            let st = sched_target(sid);
            let sd = s.store.doc(st);
            let p = fire_pending(s, k, sid, pid, next, t, deadline_s, loaded);
            assert(x.then == Some(p));
            let c = sd.schedules[sid];
            let occ = AOccurrence { at: c.next_run_at, promise_id: pid };
            let occs: Seq<AOccurrence> = seq![occ];
            assert(occs.len() == 1);
            let j = joint(loaded, sd);
            let fired = kint::spec_fire(j, sid, occs, next, t);
            lemma_fire_fold_schedules(t, j, c, occs, 1);
            let c2 = ASchedule { last_run_at: Some(c.next_run_at), next_run_at: next, ..c };
            assert(fired.schedules == sd.schedules.insert(sid, c2));
            assert(p.new == Doc { objects: Map::empty(), schedules: sd.schedules.insert(sid, c2) });
            assert(fire_shape(s.rt, o, x, sid, pid, next));
        }
    }
}

/// A request that changed nothing, answered from the read: the document is
/// as it was, and the request's run from the bucket ends related to it.
pub proof fn lemma_prepare_answered(s: Cluster, s2: Cluster, i: Id, o: Origin, req: ARequest, m: Doc)
    requires
        sys::inv()(s), sys::inv()(s2), s.rt <= kernel::MAX_TIME, ref_state(s), store_headroom(s),
        s2.store.docs == s.store.docs, s2.rt == s.rt,
        s2.nodes.contains_key(i), s2.nodes[i].txns.contains_key(o),
        s2.nodes[i].txns[o].work == Work::Request(req, m),
        request_shape(s.rt, o, s2.nodes[i].txns[o], req, m),
        s2.nodes[i].txns[o].loaded == s.store.doc(o),
        s2.nodes[i].txns[o].new == s2.nodes[i].txns[o].loaded,
        s2.log == answered(s, o, s2.nodes[i].txns[o]),
    ensures partitioned(s2), refines(s2),
{
    let x = s2.nodes[i].txns[o];
    sys::disassemble(s2);
    assert(sys::inv_txn(s2, i, o));
    lemma_bucket_same(s, s2);
    let rt = s.rt as u64;
    let acts = choose|acts: Seq<AbsAction>| explains(s, acts);
    let a = abs_run(abstract_init(), acts, rt);
    lemma_request_run(s, o, x, req, m, a);
    let racts = choose|racts: Seq<AbsAction>| request_explains(s, o, x, req, m, a, racts);
    lemma_split_doc(s, o);
    assert(glue(full(x.new), rest(s, in_origin(o), sched_in(o))) == bucket(s2));
    let res = kext::spec_handle(full(m), req, x.t).1;
    lemma_observed_push(s.log, Served { origin: o, at: x.t, req, resp: res });
    lemma_explains_step(s, s2, acts, racts, seq![response(req, res)]);
}

pub proof fn lemma_ref_prepare(s: Cluster, s2: Cluster, i: Id, o: Origin, t: nat, work: Work, new: Doc, did: bool, deadline: Option<nat>)
    requires
        sys::inv()(s), sys::inv()(s2), s.rt <= kernel::MAX_TIME, ref_state(s), store_headroom(s),
        admitted(s, Step::Prepare(i, o, t, work, new, did, deadline)),
        prepare(s, i, o, t, work, new, did, deadline) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    let n = s.nodes[i];
    let loaded = s.store.doc(o);
    let x = s2.nodes[i].txns[o];
    let changed = did || new != loaded;
    lemma_prepared_shape(s, s2, i, o, t, work, new, did, deadline);
    assert forall|q: Origin| #[trigger] s2.nodes[i].txns.contains_key(q) implies flight_shape(s.rt, q, s2.nodes[i].txns[q]) by {
        if q != o {
            assert(n.txns.contains_key(q));
        }
    }
    lemma_shapes_frame(s, s2, i);
    assert(s2.store.docs == s.store.docs && s2.rt == s.rt);
    match work {
        Work::Request(req, m) => {
            if changed {
                assert(s2.log == s.log);
                lemma_stutter_docs(s, s2);
            } else {
                assert(s2.log == answered(s, o, x));
                assert(x.work == work && x.loaded == loaded && x.new == new);
                lemma_prepare_answered(s, s2, i, o, req, m);
            }
        }
        Work::Sweep(_) => {
            assert(s2.log == s.log);
            lemma_stutter_docs(s, s2);
        }
        Work::Fire(..) => {
            assert(s2.log == s.log);
            lemma_stutter_docs(s, s2);
        }
    }
}

// ---------------------------------------------------------------------------
// The round trips, by outcome
// ---------------------------------------------------------------------------

pub proof fn lemma_ref_add_timer(s: Cluster, s2: Cluster, i: Id, o: Origin, k: AKey, out: Outcome)
    requires ref_state(s), add_timer(s, i, o, k, out) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    match out {
        Outcome::Applied => lemma_ref_arm(s, s2, i, o, k),
        Outcome::Refused => {}
        Outcome::Unknown(landed) => {
            if landed {
                let s1 = arm(s, i, o, k).unwrap();
                lemma_ref_arm(s, s1, i, o, k);
                lemma_ref_give_up(s1, s2, i, o);
            } else {
                lemma_ref_give_up(s, s2, i, o);
            }
        }
    }
}

pub proof fn lemma_ref_commit_unknown(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>, landed: bool)
    requires
        sys::inv()(s), s.rt <= kernel::MAX_TIME, ref_state(s), store_headroom(s), schedule_held(s),
        commit_unknown(s, i, o, e, landed) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    if landed {
        let s1 = commit(s, i, o, e).unwrap();
        lemma_ref_commit(s, s1, i, o, e);
        lemma_ref_give_up(s1, s2, i, o);
    } else {
        lemma_ref_give_up(s, s2, i, o);
    }
}

pub proof fn lemma_ref_process_doc(s: Cluster, s2: Cluster, i: Id, o: Origin, e: Seq<char>, out: Outcome)
    requires
        sys::inv()(s), s.rt <= kernel::MAX_TIME, ref_state(s), store_headroom(s), schedule_held(s),
        process_doc(s, i, o, e, out) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    let n = s.nodes[i];
    if s.nodes.contains_key(i) && n.txns.contains_key(o) && n.txns[o].c.changed {
        match out {
            Outcome::Applied => lemma_ref_commit(s, s2, i, o, e),
            Outcome::Refused => lemma_ref_commit_fail(s, s2, i, o),
            Outcome::Unknown(landed) => lemma_ref_commit_unknown(s, s2, i, o, e, landed),
        }
    } else {
        match out {
            Outcome::Applied => lemma_ref_collect(s, s2, i, o, e),
            Outcome::Refused => lemma_ref_collect_fail(s, s2, i, o),
            Outcome::Unknown(landed) => lemma_ref_collect_unknown(s, s2, i, o, e, landed),
        }
    }
}

pub proof fn lemma_ref_del_timer(s: Cluster, s2: Cluster, i: Id, o: Origin, prev: bool, fired: bool)
    requires sys::inv()(s), ref_state(s), del_timer(s, i, o, prev, fired) == Some(s2),
    ensures ref_state(s2), s2.rt == s.rt,
{
    lemma_pending_shaped(s, i, o);
    let s1 = if prev { disarm(s, i, o).unwrap() } else { s };
    if prev {
        lemma_ref_disarm(s, s1, i, o);
    }
    assert(pending_shaped(s1, i, o));
    lemma_ref_finish(s1, s2, i, o, fired);
}

// ---------------------------------------------------------------------------
// The induction, and the theorem
// ---------------------------------------------------------------------------

/// The empty bucket is the kernel's empty document, related to the
/// Abstract's empty state; nothing is served.
pub proof fn lemma_ref_init(s: Cluster)
    requires init()(s),
    ensures inv_ref()(s),
{
    sys::lemma_init(s);
    assert(partitioned(s));
    lemma_bucket_has(s);
    assert forall|id: Chars| !(#[trigger] bucket_objects(s).contains_key(id)) by {
        assert(s.store.doc(origin(id)) == empty_doc());
    }
    assert forall|sid: Chars| !(#[trigger] bucket_schedules(s).contains_key(sid)) by {
        assert(s.store.doc(sched_target(sid)) == empty_doc());
    }
    assert(bucket(s).objects =~= kernel_init().objects);
    assert(bucket(s).schedules =~= kernel_init().schedules);
    assert(bucket(s) == kernel_init());
    lemma_init_doc_related();
    let acts = Seq::<AbsAction>::empty();
    assert(observed(s.log) =~= Seq::<AbsResponse>::empty());
    assert(explains(s, acts));
    assert(flights_shaped(s));
}

/// Every admitted step keeps the invariant.
pub proof fn lemma_ref_next(s: Cluster, s2: Cluster)
    requires inv_ref()(s), next_admitted()(s, s2),
    ensures inv_ref()(s2),
{
    let st = choose|st: Step| #[trigger] next_step(s, s2, st) && admitted(s, st);
    assert(next()(s, s2));
    sys::lemma_next(s, s2);
    match st {
        Step::Tick(i, d) => lemma_ref_tick(s, s2, i, d),
        Step::Join(i, c) => lemma_ref_join(s, s2, i, c),
        Step::Crash(i) => lemma_ref_crash(s, s2, i),
        Step::Forget(i, o) => lemma_ref_forget(s, s2, i, o),
        Step::Prepare(i, o, t, work, new, did, deadline) => lemma_ref_prepare(s, s2, i, o, t, work, new, did, deadline),
        Step::AddTimer(i, o, k, out) => lemma_ref_add_timer(s, s2, i, o, k, out),
        Step::Process(i, o, e, out) => lemma_ref_process_doc(s, s2, i, o, e, out),
        Step::DelTimer(i, o, prev, fired) => lemma_ref_del_timer(s, s2, i, o, prev, fired),
        Step::Done(i, o) => {
            lemma_pending_shaped(s, i, o);
            lemma_ref_done(s, s2, i, o);
        }
    }
}

/// The fleet refines the Abstract: in every execution that starts in
/// `init` and steps by `next` within the doors, the requests served so far
/// are always the responses of some Abstract run from its initial state —
/// one that ends related to the bucket.
pub proof fn theorem_system_refines_abstract(spec: TempPred<Cluster>)
    requires
        spec.entails(lift_state(init())),
        spec.entails(always(lift_action(next_admitted()))),
    ensures
        spec.entails(always(lift_state(|s: Cluster| refines(s)))),
{
    assert forall|s: Cluster| #[trigger] init()(s) implies inv_ref()(s) by { lemma_ref_init(s); }
    assert forall|s: Cluster, s2: Cluster| inv_ref()(s) && #[trigger] next_admitted()(s, s2) implies inv_ref()(s2) by { lemma_ref_next(s, s2); }
    init_invariant::<Cluster>(spec, init(), next_admitted(), inv_ref());
    let p = lift_state(inv_ref());
    let q = lift_state(|s: Cluster| refines(s));
    assert forall|ex: Execution<Cluster>| #[trigger] p.implies(q).satisfied_by(ex) by {
        if p.satisfied_by(ex) {
            assert(inv_ref()(ex.head()));
            assert(refines(ex.head()));
        }
    }
    always_weaken::<Cluster>(spec, p, q);
}

} // verus!
