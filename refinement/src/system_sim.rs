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
use echod_kernel::types::{origin, AOccurrence, APromise, ARequest, ASchedule};
use echod_kernel::node::{Id, Origin};
use echod_kernel::commit::*;
use echod_system::model::*;
use echod_system::theorems as sys;
use echod_system::tla::defs::*;
use echod_system::tla::rules::*;

use crate::actions::*;
use crate::fire_sim::*;
use crate::local::*;
use crate::relation::*;
use crate::sweep_sim::*;
use crate::task_sim::doc_headroom;
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

} // verus!
