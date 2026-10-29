//! The deterministic Concrete object-store model.
//!
//! [`raw::RawStore`] is durable state: opaque key, bytes, and version only.
//! The semantic `Bucket` below remains temporarily as the decoded target used
//! by refinement; it is not stored by the raw automaton.

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]

use vstd::prelude::*;

use echod_kernel::types::{Promise, Schedule};

pub mod raw;

#[cfg(verus_keep_ghost)]
use echod_kernel::steps::executable_single_pass;
#[cfg(verus_keep_ghost)]
use echod_kernel::store::{object_order, AState};
#[cfg(verus_keep_ghost)]
use echod_kernel::types::{APromise, ASchedule};

verus! {

/// One row in a schedule document. It is explicit so origin and schedule
/// documents cannot accidentally exchange their persisted row types.
pub struct ScheduleRow {
    pub schedule: Schedule,
}

/// One persisted origin document and its write header.
pub struct OriginDocument {
    pub origin: String,
    pub rows: Vec<Promise>,
    pub stamp: u64,
    pub nonce: u64,
    pub version: u64,
}

/// One persisted schedule document and its write header.
pub struct ScheduleDocument {
    pub id: String,
    pub rows: Vec<ScheduleRow>,
    pub stamp: u64,
    pub nonce: u64,
    pub version: u64,
}

/// A deadline object in a time bucket. `key` is the store key and therefore
/// the identity used by the bucket's derived timer map.
pub struct TimerKey {
    pub key: String,
    pub bucket: u64,
    pub deadline: u64,
    pub target: String,
    pub schedule: bool,
    pub token: u64,
    pub by: String,
}

/// The body stored at `nodes/<id>`.
pub struct NodeAnnouncement {
    pub id: String,
    pub url: String,
    pub at: u64,
}

/// The body stored at `members`. Member order remains semantic because it is
/// the ownership table; it is not bucket collection order.
pub struct MembershipConfiguration {
    pub epoch: u64,
    pub members: Vec<String>,
}

/// Decoded semantic target. Vector order here is merely a representation of a
/// bucket listing and is never used as state meaning.
pub struct Bucket {
    pub origins: Vec<OriginDocument>,
    pub schedules: Vec<ScheduleDocument>,
    pub timers: Vec<TimerKey>,
    pub announcements: Vec<NodeAnnouncement>,
    pub membership: Option<MembershipConfiguration>,
}

/// Temporary decoded target for refinement. Durable state lives in
/// [`raw::RawStore`]; a codec/refinement layer may derive this semantic shape
/// from raw bytes, but the object-store automaton never stores it.
pub type SemanticBucket = Bucket;

/// The actual Concrete store is the raw object-store automaton.
pub type Store = raw::RawStore;

#[cfg(verus_keep_ghost)]
pub struct AScheduleRow {
    pub schedule: ASchedule,
}

#[cfg(verus_keep_ghost)]
pub struct AOriginDocument {
    pub origin: Seq<char>,
    pub rows: Seq<APromise>,
    pub stamp: u64,
    pub nonce: u64,
    pub version: u64,
}

#[cfg(verus_keep_ghost)]
pub struct AScheduleDocument {
    pub id: Seq<char>,
    pub rows: Seq<AScheduleRow>,
    pub stamp: u64,
    pub nonce: u64,
    pub version: u64,
}

#[cfg(verus_keep_ghost)]
pub struct ATimerKey {
    pub key: Seq<char>,
    pub bucket: u64,
    pub deadline: u64,
    pub target: Seq<char>,
    pub schedule: bool,
    pub token: u64,
    pub by: Seq<char>,
}

#[cfg(verus_keep_ghost)]
pub struct ANodeAnnouncement {
    pub id: Seq<char>,
    pub url: Seq<char>,
    pub at: u64,
}

#[cfg(verus_keep_ghost)]
pub struct AMembershipConfiguration {
    pub epoch: u64,
    pub members: Seq<Seq<char>>,
}

#[cfg(verus_keep_ghost)]
pub struct ABucket {
    pub origins: Seq<AOriginDocument>,
    pub schedules: Seq<AScheduleDocument>,
    pub timers: Seq<ATimerKey>,
    pub announcements: Seq<ANodeAnnouncement>,
    pub membership: Option<AMembershipConfiguration>,
}

#[cfg(verus_keep_ghost)]
pub type ASemanticBucket = ABucket;

#[cfg(verus_keep_ghost)]
pub type AStore = raw::ARawStore;

#[cfg(verus_keep_ghost)]
impl View for ScheduleRow {
    type V = AScheduleRow;
    open spec fn view(&self) -> AScheduleRow {
        AScheduleRow { schedule: self.schedule@ }
    }
}

#[cfg(verus_keep_ghost)]
impl View for OriginDocument {
    type V = AOriginDocument;
    open spec fn view(&self) -> AOriginDocument {
        AOriginDocument {
            origin: self.origin@,
            rows: self.rows.deep_view(),
            stamp: self.stamp,
            nonce: self.nonce,
            version: self.version,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for ScheduleDocument {
    type V = AScheduleDocument;
    open spec fn view(&self) -> AScheduleDocument {
        AScheduleDocument {
            id: self.id@,
            rows: self.rows.deep_view(),
            stamp: self.stamp,
            nonce: self.nonce,
            version: self.version,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for TimerKey {
    type V = ATimerKey;
    open spec fn view(&self) -> ATimerKey {
        ATimerKey {
            key: self.key@,
            bucket: self.bucket,
            deadline: self.deadline,
            target: self.target@,
            schedule: self.schedule,
            token: self.token,
            by: self.by@,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for NodeAnnouncement {
    type V = ANodeAnnouncement;
    open spec fn view(&self) -> ANodeAnnouncement {
        ANodeAnnouncement { id: self.id@, url: self.url@, at: self.at }
    }
}

#[cfg(verus_keep_ghost)]
impl View for MembershipConfiguration {
    type V = AMembershipConfiguration;
    open spec fn view(&self) -> AMembershipConfiguration {
        AMembershipConfiguration {
            epoch: self.epoch,
            members: self.members.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for Bucket {
    type V = ABucket;
    open spec fn view(&self) -> ABucket {
        ABucket {
            origins: self.origins.deep_view(),
            schedules: self.schedules.deep_view(),
            timers: self.timers.deep_view(),
            announcements: self.announcements.deep_view(),
            membership: self.membership.deep_view(),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for ScheduleRow {
    type V = AScheduleRow;
    open spec fn deep_view(&self) -> AScheduleRow { self@ }
}

#[cfg(verus_keep_ghost)]
impl DeepView for OriginDocument {
    type V = AOriginDocument;
    open spec fn deep_view(&self) -> AOriginDocument { self@ }
}

#[cfg(verus_keep_ghost)]
impl DeepView for ScheduleDocument {
    type V = AScheduleDocument;
    open spec fn deep_view(&self) -> AScheduleDocument { self@ }
}

#[cfg(verus_keep_ghost)]
impl DeepView for TimerKey {
    type V = ATimerKey;
    open spec fn deep_view(&self) -> ATimerKey { self@ }
}

#[cfg(verus_keep_ghost)]
impl DeepView for NodeAnnouncement {
    type V = ANodeAnnouncement;
    open spec fn deep_view(&self) -> ANodeAnnouncement { self@ }
}

#[cfg(verus_keep_ghost)]
impl DeepView for MembershipConfiguration {
    type V = AMembershipConfiguration;
    open spec fn deep_view(&self) -> AMembershipConfiguration { self@ }
}

#[cfg(verus_keep_ghost)]
impl DeepView for Bucket {
    type V = ABucket;
    open spec fn deep_view(&self) -> ABucket { self@ }
}

/// Replay one origin document's rows, last row winning.
pub open spec fn object_map(rows: Seq<APromise>) -> Map<Seq<char>, APromise>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Map::empty()
    } else {
        let p = rows.last();
        object_map(rows.drop_last()).insert(p.id, p)
    }
}

/// Replay one schedule document's rows, last row winning.
pub open spec fn schedule_row_map(
    rows: Seq<AScheduleRow>,
) -> Map<Seq<char>, ASchedule>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Map::empty()
    } else {
        let row = rows.last();
        schedule_row_map(rows.drop_last()).insert(row.schedule.id, row.schedule)
    }
}

/// Promise ids in one origin document's persisted row order.
pub open spec fn row_ids(rows: Seq<APromise>) -> Seq<Seq<char>> {
    rows.map_values(|p: APromise| p.id)
}

pub open spec fn schedule_row_ids(
    rows: Seq<AScheduleRow>,
) -> Seq<Seq<char>> {
    rows.map_values(|row: AScheduleRow| row.schedule.id)
}

pub open spec fn rows_wf(rows: Seq<APromise>) -> bool {
    row_ids(rows).no_duplicates()
}

pub open spec fn schedule_rows_wf(rows: Seq<AScheduleRow>) -> bool {
    schedule_row_ids(rows).no_duplicates()
}

pub open spec fn origin_document_wf(document: AOriginDocument) -> bool {
    &&& rows_wf(document.rows)
    &&& forall|i: int| 0 <= i < document.rows.len()
        ==> echod_kernel::types::origin(#[trigger] document.rows[i].id)
            == document.origin
}

pub open spec fn schedule_document_wf(document: AScheduleDocument) -> bool {
    &&& schedule_rows_wf(document.rows)
    &&& forall|i: int| 0 <= i < document.rows.len()
        ==> #[trigger] document.rows[i].schedule.id == document.id
}

pub open spec fn origin_keys(
    documents: Seq<AOriginDocument>,
) -> Seq<Seq<char>> {
    documents.map_values(|document: AOriginDocument| document.origin)
}

pub open spec fn schedule_keys(
    documents: Seq<AScheduleDocument>,
) -> Seq<Seq<char>> {
    documents.map_values(|document: AScheduleDocument| document.id)
}

pub open spec fn timer_keys(keys: Seq<ATimerKey>) -> Seq<Seq<char>> {
    keys.map_values(|key: ATimerKey| key.key)
}

pub open spec fn announcement_keys(
    announcements: Seq<ANodeAnnouncement>,
) -> Seq<Seq<char>> {
    announcements.map_values(|announcement: ANodeAnnouncement| announcement.id)
}

/// Derived keyed views. Reordering a bucket collection does not change the
/// intended meaning of any of these maps.
pub open spec fn origin_document_map(
    documents: Seq<AOriginDocument>,
) -> Map<Seq<char>, AOriginDocument>
    decreases documents.len(),
{
    if documents.len() == 0 {
        Map::empty()
    } else {
        let document = documents.last();
        origin_document_map(documents.drop_last()).insert(
            document.origin, document,
        )
    }
}

pub open spec fn schedule_document_map(
    documents: Seq<AScheduleDocument>,
) -> Map<Seq<char>, AScheduleDocument>
    decreases documents.len(),
{
    if documents.len() == 0 {
        Map::empty()
    } else {
        let document = documents.last();
        schedule_document_map(documents.drop_last()).insert(
            document.id, document,
        )
    }
}

pub open spec fn timer_map(
    keys: Seq<ATimerKey>,
) -> Map<Seq<char>, ATimerKey>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Map::empty()
    } else {
        let key = keys.last();
        timer_map(keys.drop_last()).insert(key.key, key)
    }
}

pub open spec fn announcement_map(
    announcements: Seq<ANodeAnnouncement>,
) -> Map<Seq<char>, ANodeAnnouncement>
    decreases announcements.len(),
{
    if announcements.len() == 0 {
        Map::empty()
    } else {
        let announcement = announcements.last();
        announcement_map(announcements.drop_last()).insert(
            announcement.id, announcement,
        )
    }
}

pub open spec fn bucket_wf(bucket: ABucket) -> bool {
    &&& origin_keys(bucket.origins).no_duplicates()
    &&& schedule_keys(bucket.schedules).no_duplicates()
    &&& timer_keys(bucket.timers).no_duplicates()
    &&& announcement_keys(bucket.announcements).no_duplicates()
    &&& forall|i: int| 0 <= i < bucket.origins.len()
        ==> origin_document_wf(#[trigger] bucket.origins[i])
    &&& forall|i: int| 0 <= i < bucket.schedules.len()
        ==> schedule_document_wf(#[trigger] bucket.schedules[i])
    &&& match bucket.membership {
        Some(configuration) => configuration.members.no_duplicates(),
        None => true,
    }
}

/// The kernel view of one origin document. Bucket order is outside this
/// operation; the kernel's executable order witness is local to `rows`.
pub open spec fn kernel_view(document: AOriginDocument) -> AState {
    AState {
        objects: object_map(document.rows),
        schedules: Map::empty(),
        outbox: Map::empty(),
    }
}

impl Bucket {
    pub fn new() -> (bucket: Bucket)
        ensures
            bucket@.origins == Seq::<AOriginDocument>::empty(),
            bucket@.schedules == Seq::<AScheduleDocument>::empty(),
            bucket@.timers == Seq::<ATimerKey>::empty(),
            bucket@.announcements == Seq::<ANodeAnnouncement>::empty(),
            bucket@.membership is None,
            bucket_wf(bucket@),
    {
        Bucket {
            origins: Vec::new(),
            schedules: Vec::new(),
            timers: Vec::new(),
            announcements: Vec::new(),
            membership: None,
        }
    }
}

/// Refresh existing rows from a kernel result without changing local order.
pub open spec fn refresh_rows(
    rows: Seq<APromise>,
    objects: Map<Seq<char>, APromise>,
) -> Seq<APromise>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        let p = rows.last();
        refresh_rows(rows.drop_last(), objects).push(
            if objects.contains_key(p.id) { objects[p.id] } else { p },
        )
    }
}

/// Append one newly born promise to its origin document.
pub open spec fn append_birth(
    rows: Seq<APromise>,
    before: Map<Seq<char>, APromise>,
    after: Map<Seq<char>, APromise>,
    id: Seq<char>,
) -> Seq<APromise> {
    let updated = refresh_rows(rows, after);
    if !before.contains_key(id) && after.contains_key(id) {
        updated.push(after[id])
    } else {
        updated
    }
}

/// Concrete's exact one-pass normalization in one document's persisted order.
/// Header metadata is unchanged until the surrounding commit writes a version.
pub open spec fn normalize(
    document: AOriginDocument,
    now: nat,
    retry_timeout: nat,
) -> AOriginDocument {
    let before = kernel_view(document);
    let after = executable_single_pass(
        before,
        row_ids(document.rows),
        now,
        retry_timeout,
    );
    AOriginDocument {
        rows: refresh_rows(document.rows, after.objects),
        ..document
    }
}

pub proof fn lemma_row_ids_refresh(
    rows: Seq<APromise>,
    objects: Map<Seq<char>, APromise>,
)
    requires
        forall|i: int| 0 <= i < rows.len()
            ==> objects.contains_key(#[trigger] rows[i].id)
                && objects[rows[i].id].id == rows[i].id,
    ensures
        row_ids(refresh_rows(rows, objects)) == row_ids(rows),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_row_ids_refresh(rows.drop_last(), objects);
        let p = rows.last();
        assert(objects.contains_key(p.id));
        assert(objects[p.id].id == p.id);
        assert(refresh_rows(rows, objects)
            == refresh_rows(rows.drop_last(), objects).push(objects[p.id]));
        assert(row_ids(rows) == row_ids(rows.drop_last()).push(p.id));
    }
}

pub proof fn lemma_object_map_contains(rows: Seq<APromise>, id: Seq<char>)
    ensures
        object_map(rows).contains_key(id) <==> row_ids(rows).contains(id),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_object_map_contains(rows.drop_last(), id);
        let p = rows.last();
        assert(row_ids(rows) == row_ids(rows.drop_last()).push(p.id));
        assert(object_map(rows) == object_map(rows.drop_last()).insert(p.id, p));
        assert(row_ids(rows).contains(id)
            <==> (row_ids(rows.drop_last()).contains(id) || p.id == id)) by {
            if row_ids(rows).contains(id) {
                let i = choose|i: int| 0 <= i < row_ids(rows).len()
                    && row_ids(rows)[i] == id;
                if i < row_ids(rows).len() - 1 {
                    assert(row_ids(rows.drop_last())[i] == id);
                }
            }
            if row_ids(rows.drop_last()).contains(id) {
                let i = choose|i: int| 0 <= i < row_ids(rows.drop_last()).len()
                    && row_ids(rows.drop_last())[i] == id;
                assert(row_ids(rows)[i] == id);
            }
            if p.id == id {
                assert(row_ids(rows)[rows.len() - 1] == id);
            }
        }
    }
}

/// A well-formed origin document supplies its kernel order witness.
pub proof fn lemma_rows_are_object_order(document: AOriginDocument)
    requires
        origin_document_wf(document),
    ensures
        object_order(kernel_view(document), row_ids(document.rows)),
{
    assert(row_ids(document.rows).no_duplicates());
    assert forall|i: int| 0 <= i < row_ids(document.rows).len()
        implies kernel_view(document).objects.contains_key(
            #[trigger] row_ids(document.rows)[i],
        ) by {
        lemma_object_map_contains(document.rows, row_ids(document.rows)[i]);
        assert(row_ids(document.rows).contains(row_ids(document.rows)[i]));
    }
    assert forall|id: Seq<char>|
        #[trigger] kernel_view(document).objects.contains_key(id)
        implies row_ids(document.rows).contains(id) by {
        lemma_object_map_contains(document.rows, id);
    }
}

} // verus!
