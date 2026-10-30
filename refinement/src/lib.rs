//! Local Concrete-to-Abstract refinement.
//!
//! This crate depends on the two model levels, not on a checker framework.
//! Concrete owns document-local persisted row order; Abstract owns independent
//! protocol objects and actions. Bucket listing order is erased at this
//! refinement boundary by comparing derived keyed meanings.

#![cfg(verus_keep_ghost)]
#![allow(unused_imports)]

pub mod bridge;
pub mod heartbeat_sim;
pub mod promise_sim;
pub mod read_sim;
pub mod relation;
pub mod schedule_sim;
pub mod task_sim;

use vstd::prelude::*;

use echod_abstract::state as abs_state;
use echod_abstract::types as abs;
use echod_concrete::{
    bucket_wf, derived::decode_bucket_spec, raw::{ARawObject, ARawStore},
    AOriginDocument, AScheduleDocument, AScheduleRow, ASemanticBucket,
};
use echod_kernel::types as kernel;
use echod_kernel::types::{
    APromise, ASchedule, ATask, AValue,
};

verus! {

pub type Chars = Seq<char>;

/// Everything after the first `:`, or empty for a root id.
pub open spec fn suffix(id: Chars) -> Chars
    decreases id.len(),
{
    if id.len() == 0 {
        Seq::empty()
    } else if id[0] == ':' {
        id.drop_first()
    } else {
        suffix(id.drop_first())
    }
}

pub open spec fn text(chars: Chars) -> abs::AText {
    abs::AText { chars }
}

pub open spec fn ident(id: Chars) -> abs::AIdent {
    abs::AIdent {
        origin: text(kernel::origin(id)),
        suffix: text(suffix(id)),
    }
}

pub open spec fn tag(pair: (Chars, Chars)) -> abs::ATag {
    abs::ATag {
        key: text(pair.0),
        value: text(pair.1),
    }
}

pub open spec fn tags(xs: Seq<(Chars, Chars)>) -> Seq<abs::ATag>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else {
        tags(xs.drop_last()).push(tag(xs.last()))
    }
}

pub open spec fn value(v: AValue) -> abs::AValue {
    abs::AValue {
        headers: tags(v.headers),
        data: match v.data {
            Some(x) => Some(text(x)),
            None => None,
        },
    }
}

pub open spec fn promise_state(
    state: kernel::PromiseState,
) -> abs::PromiseState {
    match state {
        kernel::PromiseState::Pending => abs::PromiseState::Pending,
        kernel::PromiseState::Resolved => abs::PromiseState::Resolved,
        kernel::PromiseState::Rejected => abs::PromiseState::Rejected,
        kernel::PromiseState::RejectedCanceled =>
            abs::PromiseState::RejectedCanceled,
        kernel::PromiseState::RejectedTimedout =>
            abs::PromiseState::RejectedTimedout,
    }
}

pub open spec fn task_state(state: kernel::TaskState) -> abs::TaskState {
    match state {
        kernel::TaskState::Pending => abs::TaskState::Pending,
        kernel::TaskState::Acquired => abs::TaskState::Acquired,
        kernel::TaskState::Suspended => abs::TaskState::Suspended,
        kernel::TaskState::Halted => abs::TaskState::Halted,
        kernel::TaskState::Fulfilled => abs::TaskState::Fulfilled,
    }
}

pub open spec fn id_list(ids: Seq<Chars>) -> Seq<abs::AIdent>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        id_list(ids.drop_last()).push(ident(ids.last()))
    }
}

pub open spec fn text_list(xs: Seq<Chars>) -> Seq<abs::AText>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else {
        text_list(xs.drop_last()).push(text(xs.last()))
    }
}

pub open spec fn task(t: ATask) -> abs_state::ATaskObject {
    abs_state::ATaskObject {
        state: task_state(t.state),
        version: t.version,
        ttl: t.ttl,
        pid: match t.pid {
            Some(x) => Some(text(x)),
            None => None,
        },
        lease_timeout_at: t.lease_timeout_at,
        retry_timeout_at: t.retry_timeout_at,
        resumes: id_list(t.resumes),
    }
}

pub open spec fn promise(p: APromise) -> abs_state::APromiseObject {
    abs_state::APromiseObject {
        state: promise_state(p.state),
        param: value(p.param),
        value: value(p.value),
        tags: tags(p.tags),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
        callbacks: id_list(p.callbacks),
        listeners: text_list(p.listeners),
    }
}

pub open spec fn object(p: APromise) -> abs_state::AObject {
    abs_state::AObject {
        id: ident(p.id),
        promise: promise(p),
        task: match p.task {
            Some(t) => Some(task(t)),
            None => None,
        },
    }
}

pub open spec fn schedule(row: ASchedule) -> abs::ASchedule {
    abs::ASchedule {
        id: ident(row.id),
        cron: text(row.cron),
        promise_id: ident(row.promise_id),
        promise_timeout: row.promise_timeout,
        promise_param: value(row.promise_param),
        promise_tags: tags(row.promise_tags),
        next_run_at: row.next_run_at,
        last_run_at: row.last_run_at,
        created_at: row.created_at,
    }
}

pub open spec fn objects(rows: Seq<APromise>) -> Seq<abs_state::AObject>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        objects(rows.drop_last()).push(object(rows.last()))
    }
}

pub open spec fn schedule_rows(
    rows: Seq<AScheduleRow>,
) -> Seq<abs::ASchedule>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        schedule_rows(rows.drop_last()).push(schedule(rows.last().schedule))
    }
}

/// Fold every origin document. This sequence is only a rendering for the
/// independent Abstract state; its cross-document order is not compared.
pub open spec fn document_objects(
    documents: Seq<AOriginDocument>,
) -> Seq<abs_state::AObject>
    decreases documents.len(),
{
    if documents.len() == 0 {
        Seq::empty()
    } else {
        document_objects(documents.drop_last()) + objects(documents.last().rows)
    }
}

/// Fold every schedule document and every explicit schedule row.
pub open spec fn document_schedules(
    documents: Seq<AScheduleDocument>,
) -> Seq<abs::ASchedule>
    decreases documents.len(),
{
    if documents.len() == 0 {
        Seq::empty()
    } else {
        document_schedules(documents.drop_last())
            + schedule_rows(documents.last().rows)
    }
}

/// Abstract object-list order is not semantic. Handlers address objects by
/// id and searches are explicitly unsupported, so refinement compares the
/// keyed contents while Concrete retains its own persisted row order.
pub open spec fn abstract_object_map(
    rows: Seq<abs_state::AObject>,
) -> Map<abs::AIdent, abs_state::AObject>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Map::empty()
    } else {
        let object = rows.last();
        abstract_object_map(rows.drop_last()).insert(object.id, object)
    }
}

pub open spec fn abstract_ids(
    rows: Seq<abs_state::AObject>,
) -> Seq<abs::AIdent> {
    rows.map_values(|object: abs_state::AObject| object.id)
}

pub open spec fn abstract_schedule_map(
    rows: Seq<abs::ASchedule>,
) -> Map<abs::AIdent, abs::ASchedule>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Map::empty()
    } else {
        let schedule = rows.last();
        abstract_schedule_map(rows.drop_last()).insert(schedule.id, schedule)
    }
}

pub open spec fn abstract_schedule_ids(
    rows: Seq<abs::ASchedule>,
) -> Seq<abs::AIdent> {
    rows.map_values(|schedule: abs::ASchedule| schedule.id)
}

pub open spec fn abstract_of(store: ASemanticBucket) -> abs_state::AState {
    abs_state::AState {
        objects: document_objects(store.origins),
        schedules: document_schedules(store.schedules),
        outbox: Seq::empty(),
    }
}

/// The semantic half of refinement, after raw bytes have been decoded.
/// The order of origins and schedules in either bucket/list representation
/// is immaterial.
pub open spec fn semantic_related(
    concrete: ASemanticBucket,
    abstract_state: abs_state::AState,
) -> bool {
    &&& bucket_wf(concrete)
    &&& abstract_ids(abstract_state.objects).no_duplicates()
    &&& abstract_schedule_ids(abstract_state.schedules).no_duplicates()
    &&& abstract_object_map(abstract_state.objects)
        == abstract_object_map(document_objects(concrete.origins))
    &&& abstract_schedule_map(abstract_state.schedules)
        == abstract_schedule_map(document_schedules(concrete.schedules))
    &&& abstract_state.outbox == Seq::<abs_state::AOutboxEntry>::empty()
}

/// A raw store is a well-formed Concrete state only when every key and body
/// decodes and the resulting semantic bucket satisfies its local invariants.
/// Thus malformed and noncanonical bytes are outside the Concrete state
/// space, rather than being related to an arbitrary Abstract state.
pub open spec fn concrete_wf(
    concrete: ARawStore,
    prefix: Seq<u8>,
    bucket_ms: u64,
) -> bool {
    &&& concrete.keys == concrete.entries.map_values(
        |entry: echod_concrete::raw::AEntry| entry.key,
    )
    &&& concrete.keys.no_duplicates()
    &&& concrete.next_version > 0
    &&& forall|i: int| 0 <= i < concrete.entries.len()
        ==> concrete.entries[i].object.version < concrete.next_version
    &&& match decode_bucket_spec(concrete, prefix, bucket_ms) {
        Some(decoded) => bucket_wf(decoded),
        None => false,
    }
}

/// The primary refinement relation is explicitly RawStore -> decoded
/// SemanticBucket -> Abstract.
pub open spec fn related(
    concrete: ARawStore,
    prefix: Seq<u8>,
    bucket_ms: u64,
    abstract_state: abs_state::AState,
) -> bool {
    &&& concrete_wf(concrete, prefix, bucket_ms)
    &&& match decode_bucket_spec(concrete, prefix, bucket_ms) {
        Some(decoded) => semantic_related(decoded, abstract_state),
        None => false,
    }
}

pub open spec fn semantic_init() -> ASemanticBucket {
    ASemanticBucket {
        origins: Seq::empty(),
        schedules: Seq::empty(),
        timers: Seq::empty(),
        announcements: Seq::empty(),
        membership: None,
    }
}

pub open spec fn concrete_init(bucket: Chars) -> ARawStore {
    ARawStore {
        bucket,
        entries: Seq::empty(),
        objects: Map::<Seq<u8>, ARawObject>::empty(),
        keys: Seq::empty(),
        next_version: 1,
    }
}

pub open spec fn abstract_init() -> abs_state::AState {
    abs_state::AState {
        objects: Seq::empty(),
        schedules: Seq::empty(),
        outbox: Seq::empty(),
    }
}

pub proof fn lemma_objects_len(rows: Seq<APromise>)
    ensures
        objects(rows).len() == rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_objects_len(rows.drop_last());
    }
}

pub proof fn lemma_schedule_rows_len(rows: Seq<AScheduleRow>)
    ensures
        schedule_rows(rows).len() == rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_schedule_rows_len(rows.drop_last());
    }
}

pub proof fn lemma_init_related(
    bucket: Chars,
    prefix: Seq<u8>,
    bucket_ms: u64,
)
    ensures
        concrete_wf(concrete_init(bucket), prefix, bucket_ms),
        related(
            concrete_init(bucket), prefix, bucket_ms, abstract_init(),
        ),
{
    assert(concrete_init(bucket).keys
        == concrete_init(bucket).entries.map_values(
            |entry: echod_concrete::raw::AEntry| entry.key,
        ));
    assert(concrete_init(bucket).keys.no_duplicates());
    assert forall|i: int| 0 <= i < concrete_init(bucket).entries.len()
        implies concrete_init(bucket).entries[i].object.version
            < concrete_init(bucket).next_version by {}
    assert(decode_bucket_spec(
        concrete_init(bucket), prefix, bucket_ms,
    ) == Some(semantic_init()));
    assert(bucket_wf(semantic_init()));
    assert(concrete_wf(concrete_init(bucket), prefix, bucket_ms));
    assert(abstract_ids(Seq::<abs_state::AObject>::empty()).no_duplicates());
    assert(abstract_schedule_ids(Seq::<abs::ASchedule>::empty()).no_duplicates());
    assert(semantic_related(semantic_init(), abstract_init()));
    assert(related(
        concrete_init(bucket), prefix, bucket_ms, abstract_init(),
    ));
}

} // verus!
