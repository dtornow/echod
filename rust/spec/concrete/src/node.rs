//! One node. A request or a due document is a flight: load the document,
//! decide, write it back, then answer. The store keeps the bytes. Nothing
//! here calls the abstract model.
//!
//! The executable node first, inside `verus!`, each function carrying the
//! `spec_*` twin it computes; then the node as a specification, over the
//! view types: `NodeV`, `DocumentBodyV`, the `spec_*` twins of its handlers and steps.
//!
//! Trusted here: the JSON codec computes `spec_encode_body` / `spec_read`
//! (`encode`, `decode`), the key hash computes `spec_fnv` (`hash_key`, over
//! the store's `fnv1a`), a string is its characters (`chars_of`), a copy of a
//! sorted table is that table (`Objects::clone`), and the cron engine and the
//! id template are the abstract crate's `next_cron` and `expand`. Everything
//! else Verus checks: `Node::step` computes `spec_node`, and `Node::new`
//! computes `spec_initial_node`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::pervasive::VecAdditionalExecFns;
use vstd::prelude::*;

use echod_types::{
    deadline_bounded, origin_of, same_origin, PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq,
    PromiseRes, PromiseSettleReq, PromiseState, Request, Response, Schedule, ScheduleCreateReq,
    ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceAction, TaskFenceInnerRes, TaskFenceRes,
    TaskGetRes, TaskRecord, TaskRef, TaskState, Value, MAX_TIME, MAX_VERSION,
};

use echod_abstract::trusted::{copy, expand, next_cron};
#[cfg(verus_keep_ghost)]
use echod_abstract::trusted::{axiom_string_ext, axiom_vec_ext};
#[cfg(verus_keep_ghost)]
use echod_abstract::machine::{lemma_tags_ext, lemma_value_ext};
use echod_abstract::{Call, Dispatch, Output};
use echod_rover::rover::ProcessEvent;
#[cfg(verus_keep_ghost)]
use echod_rover::rover::semantics::StepResultV;
use echod_rover::Time;
#[cfg(verus_keep_ghost)]
use echod_types::{origin, same_origin_spec, spec_deadline_bounded, AValue};

#[cfg(verus_keep_ghost)]
use crate::model::{
    spec_bytes, spec_clock, spec_get, spec_initial_node, spec_node, spec_notes, spec_notify,
    spec_one, spec_reply, spec_string, LocalV,
};
use crate::model::{Fleet, Logic, LogicV, Message, Pid};
pub use crate::document::{
    DocumentBody, DocumentBodyV, LoadedDocument, LoadedDocumentV, Obj, ObjV, Objects, Prom,
    PromV, ScheduleDocument, ScheduleDocumentV, StoredDocument, StoredDocumentV, Tk, TkV,
    WorkflowDocument, WorkflowDocumentV,
};
#[cfg(verus_keep_ghost)]
use crate::store::{spec_before, spec_fnv, spec_sat_add, spec_starts, Read, StoreError};
use crate::store::{fnv1a, Etag, StoreReq, StoreRes};

verus! {

broadcast use vstd::seq::group_seq_lemmas, vstd::set::group_set_lemmas;

// ---------------------------------------------------------------------------
// The node, executed
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Node {
    /// The process shell: clock and flags.
    pub logic: Logic,
    /// When the next timeout is worth delivering.
    pub wake: Option<u64>,
    pub next_request: u64,
    address: u64,
    nodes: u64,
    /// How long a pending task waits before it is offered again.
    retry_timeout: u64,
    flight: Option<Flight>,
    /// Each document once, in the order it was first remembered.
    cache: Vec<Cached>,
    /// The occurrences owed, oldest first.
    pending: Vec<Pending>,
    next_op: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
struct Cached {
    key: String,
    doc: DocumentBody,
    etag: Option<Etag>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
struct Flight {
    op: u64,
    key: String,
    /// Whether the flight is writing the document back.
    writing: bool,
    job: Job,
    etag: Option<Etag>,
    /// The clock of the event that opened the flight.
    now: u64,
    /// The client a request flight answers: its name and the call id.
    caller: Option<(String, u64)>,
    /// The document a write is putting, installed in the cache when it lands.
    decided: Option<DocumentBody>,
    /// Occurrences a schedule step queued, delivered to the pending list when the write lands.
    born: Vec<Pending>,
    reply: Option<(String, u64, Response)>,
    /// Boundary output of a due step, sent when that step's document is committed.
    notify: Vec<Outbound>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
enum Job {
    External { request: Request },
    Due,
    Occurrence(Pending),
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Pending {
    pub promise: String,
    pub at: u64,
    pub timeout: u64,
    pub param: Value,
    pub tags: Tags,
}

/// A copy of a sorted table is sorted: the derived clone, with its invariant kept.
impl Clone for Objects {
    #[verifier::external_body]
    fn clone(&self) -> (r: Self)
        ensures
            r == *self,
    {
        Objects { entries: self.entries.clone() }
    }
}

/// What a due step tells the outside, once the document that step wrote is the one in the cache.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Outbound {
    /// A pending task is offered again.
    Execute { id: String, version: u64 },
    /// A listener's promise has settled.
    Unblock { address: String, promise: PromiseRecord },
}

// ---------------------------------------------------------------------------
// Views: the exec node as the specification sees it
// ---------------------------------------------------------------------------

spec fn strs_v(v: Seq<String>) -> Seq<Seq<char>> {
    v.map_values(|s: String| s@)
}

impl View for Prom {
    type V = PromV;
    closed spec fn view(&self) -> PromV {
        PromV {
            state: self.state,
            param: self.param,
            value: self.value,
            tags: self.tags,
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
            callbacks: strs_v(self.callbacks@),
            listeners: strs_v(self.listeners@),
        }
    }
}

impl View for Tk {
    type V = TkV;
    closed spec fn view(&self) -> TkV {
        TkV {
            state: self.state,
            version: self.version,
            pid: match self.pid { Some(s) => Some(s@), None => None },
            ttl: self.ttl,
            lease_timeout_at: self.lease_timeout_at,
            retry_timeout_at: self.retry_timeout_at,
            resumes: strs_v(self.resumes@),
        }
    }
}

impl View for Obj {
    type V = ObjV;
    closed spec fn view(&self) -> ObjV {
        ObjV {
            promise: self.promise@,
            task: match self.task { Some(t) => Some(t@), None => None },
        }
    }
}

spec fn spec_has_key(entries: Seq<(String, Obj)>, k: Seq<char>) -> bool {
    exists|i: int| 0 <= i < entries.len() && #[trigger] entries[i].0@ == k
}

spec fn spec_index(entries: Seq<(String, Obj)>, k: Seq<char>) -> int {
    choose|i: int| 0 <= i < entries.len() && #[trigger] entries[i].0@ == k
}

pub open spec fn spec_keys_of(entries: Seq<(String, Obj)>) -> Seq<Seq<char>> {
    entries.map_values(|e: (String, Obj)| e.0@)
}

/// The entries as a map from id to object.
spec fn spec_objs(entries: Seq<(String, Obj)>) -> Map<Seq<char>, ObjV> {
    Map::new(spec_keys_of(entries).to_set(), |k: Seq<char>| entries[spec_index(entries, k)].1@)
}

/// Strictly increasing keys.
/// The entries put in turn, a later id replacing an earlier one.
pub open spec fn spec_from_entries(entries: Seq<(String, Obj)>) -> Map<Seq<char>, ObjV>
    decreases entries.len(),
{
    if entries.len() == 0 {
        Map::empty()
    } else {
        spec_from_entries(entries.drop_last()).insert(entries.last().0@, entries.last().1@)
    }
}

proof fn lemma_from_entries_prefix(entries: Seq<(String, Obj)>, i: int)
    requires
        i == 0,
    ensures
        spec_from_entries(entries.take(i)) == Map::<Seq<char>, ObjV>::empty(),
{
    assert(entries.take(0).len() == 0);
}

proof fn lemma_from_entries_step(entries: Seq<(String, Obj)>, i: int)
    requires
        0 <= i < entries.len(),
    ensures
        spec_from_entries(entries.take(i + 1)) == spec_from_entries(entries.take(i)).insert(entries[i].0@, entries[i].1@),
{
    assert(entries.take(i + 1).drop_last() =~= entries.take(i));
    assert(entries.take(i + 1).last() == entries[i]);
}

/// A table with distinct keys is the put of its entries.
proof fn lemma_from_entries_sorted(entries: Seq<(String, Obj)>)
    requires
        spec_sorted_entries(entries),
    ensures
        spec_from_entries(entries) == spec_objs(entries),
    decreases entries.len(),
{
    if entries.len() == 0 {
        assert(spec_keys_of(entries) =~= Seq::<Seq<char>>::empty());
        assert(spec_keys_of(entries).to_set() =~= Set::<Seq<char>>::empty());
        assert(spec_objs(entries) =~= Map::<Seq<char>, ObjV>::empty());
    } else {
        let front = entries.drop_last();
        let e = entries.last();
        lemma_from_entries_sorted(front);
        lemma_objs_insert(front, front.len() as int, e);
        assert(front.insert(front.len() as int, e) =~= entries);
    }
}

pub open spec fn spec_sorted_entries(entries: Seq<(String, Obj)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < entries.len() ==> spec_before(#[trigger] entries[i].0@, #[trigger] entries[j].0@)
}

impl Objects {
    #[verifier::type_invariant]
    closed spec fn wf(&self) -> bool {
        spec_sorted_entries(self.entries@)
    }
}

impl View for Objects {
    type V = Map<Seq<char>, ObjV>;
    closed spec fn view(&self) -> Map<Seq<char>, ObjV> {
        spec_objs(self.entries@)
    }
}

impl View for DocumentBody {
    type V = DocumentBodyV;
    closed spec fn view(&self) -> DocumentBodyV {
        match self {
            DocumentBody::Workflow(objs) => DocumentBodyV::Workflow(objs@),
            DocumentBody::Schedule(slot) => DocumentBodyV::Schedule(*slot),
        }
    }
}

impl View for WorkflowDocument {
    type V = WorkflowDocumentV;
    closed spec fn view(&self) -> WorkflowDocumentV {
        WorkflowDocumentV {
            document: self.document@,
            version: self.version,
            committed_at: self.committed_at,
            next_wake_at: self.next_wake_at,
            objects: self.objects@,
        }
    }
}

impl View for ScheduleDocument {
    type V = ScheduleDocumentV;
    closed spec fn view(&self) -> ScheduleDocumentV {
        ScheduleDocumentV {
            document: self.document@,
            version: self.version,
            committed_at: self.committed_at,
            next_wake_at: self.next_wake_at,
            schedule: self.schedule,
        }
    }
}

impl View for StoredDocument {
    type V = StoredDocumentV;
    closed spec fn view(&self) -> StoredDocumentV {
        match self {
            StoredDocument::Workflow(doc) => StoredDocumentV::Workflow(doc@),
            StoredDocument::Schedule(doc) => StoredDocumentV::Schedule(doc@),
        }
    }
}

/// The executable enum carrier and its closed logical view select the same
/// document family.
pub proof fn lemma_stored_document_variant_view(
    document: &StoredDocument,
)
    ensures
        match document {
            StoredDocument::Workflow(_) => document.deep_view() is Workflow,
            StoredDocument::Schedule(_) => document.deep_view() is Schedule,
        },
{
    match document {
        StoredDocument::Workflow(_) => {},
        StoredDocument::Schedule(_) => {},
    }
}

impl View for LoadedDocument {
    type V = LoadedDocumentV;
    open spec fn view(&self) -> LoadedDocumentV {
        LoadedDocumentV {
            document: self.document@,
            change_count: self.change_count,
            bytes: self.bytes,
            append_certified: self.append_certified,
        }
    }
}

impl DeepView for LoadedDocument {
    type V = LoadedDocumentV;
    open spec fn deep_view(&self) -> LoadedDocumentV {
        self.view()
    }
}

impl View for Pending {
    type V = PendingV;
    closed spec fn view(&self) -> PendingV {
        PendingV { promise: self.promise@, at: self.at, timeout: self.timeout, param: self.param, tags: self.tags }
    }
}

impl DeepView for DocumentBody {
    type V = DocumentBodyV;
    open spec fn deep_view(&self) -> DocumentBodyV {
        self.view()
    }
}

impl DeepView for StoredDocument {
    type V = StoredDocumentV;
    open spec fn deep_view(&self) -> StoredDocumentV {
        self.view()
    }
}

impl DeepView for Pending {
    type V = PendingV;
    open spec fn deep_view(&self) -> PendingV {
        self.view()
    }
}

impl View for Outbound {
    type V = NoteV;
    closed spec fn view(&self) -> NoteV {
        match self {
            Outbound::Execute { id, version } => NoteV::Execute { id: id@, version: *version },
            Outbound::Unblock { address, promise } => NoteV::Unblock { address: address@, promise: *promise },
        }
    }
}

impl View for Job {
    type V = JobV;
    closed spec fn view(&self) -> JobV {
        match self {
            Job::External { request } => JobV::External(*request),
            Job::Due => JobV::Due,
            Job::Occurrence(pending) => JobV::Occurrence(pending@),
        }
    }
}

spec fn etag_v(etag: Option<Etag>) -> Option<Seq<char>> {
    match etag { Some(tag) => Some(tag.0@), None => None }
}

spec fn caller_v(caller: Option<(String, u64)>) -> Option<(Seq<char>, u64)> {
    match caller { Some((client, id)) => Some((client@, id)), None => None }
}

spec fn reply_v(reply: Option<(String, u64, Response)>) -> Option<(Seq<char>, u64, Response)> {
    match reply { Some((client, id, response)) => Some((client@, id, response)), None => None }
}

pub open spec fn pend_v(v: Seq<Pending>) -> Seq<PendingV> {
    v.map_values(|p: Pending| p@)
}

pub open spec fn notes_v(v: Seq<Outbound>) -> Seq<NoteV> {
    v.map_values(|n: Outbound| n@)
}

spec fn docs_v(v: Seq<Cached>) -> Seq<CachedV> {
    v.map_values(|c: Cached| c@)
}

impl View for Cached {
    type V = CachedV;
    closed spec fn view(&self) -> CachedV {
        CachedV { key: self.key@, body: spec_encode_body(self.doc@), etag: etag_v(self.etag) }
    }
}

impl View for Flight {
    type V = FlightV;
    closed spec fn view(&self) -> FlightV {
        FlightV {
            op: self.op,
            key: self.key@,
            writing: self.writing,
            etag: etag_v(self.etag),
            now: self.now,
            caller: caller_v(self.caller),
            job: self.job@,
            born: pend_v(self.born@),
            reply: reply_v(self.reply),
            notify: notes_v(self.notify@),
            decided: match self.decided { Some(doc) => Some(spec_encode_body(doc@)), None => None },
        }
    }
}

impl View for Node {
    type V = NodeV;
    closed spec fn view(&self) -> NodeV {
        NodeV {
            logic: self.logic@,
            wake: match self.wake { Some(t) => Some(t as nat), None => None },
            next_request: self.next_request,
            address: self.address as nat,
            nodes: self.nodes as nat,
            retry_timeout: self.retry_timeout,
            flight: match self.flight { Some(f) => Some(f@), None => None },
            documents: docs_v(self.cache@),
            pending: pend_v(self.pending@),
            next_op: self.next_op,
        }
    }
}

// ---------------------------------------------------------------------------
// The key order
// ---------------------------------------------------------------------------

proof fn lemma_before_irrefl(a: Seq<char>)
    ensures
        !spec_before(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_before_irrefl(a.drop_first());
    }
}

proof fn lemma_before_trans(a: Seq<char>, b: Seq<char>, c: Seq<char>)
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

proof fn lemma_before_total(a: Seq<char>, b: Seq<char>)
    requires
        a != b,
    ensures
        spec_before(a, b) || spec_before(b, a),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        if b.len() == 0 {
            assert(a =~= b);
        }
    } else if b.len() == 0 {
    } else if a[0] != b[0] {
        assert(a[0] < b[0] || b[0] < a[0]);
    } else {
        assert(a =~= seq![a[0]] + a.drop_first());
        assert(b =~= seq![b[0]] + b.drop_first());
        if a.drop_first() == b.drop_first() {
            assert(a == b);
        }
        lemma_before_total(a.drop_first(), b.drop_first());
    }
}

proof fn lemma_before_asym(a: Seq<char>, b: Seq<char>)
    requires
        spec_before(a, b),
    ensures
        !spec_before(b, a),
{
    if spec_before(b, a) {
        lemma_before_trans(a, b, a);
        lemma_before_irrefl(a);
    }
}

/// A key is in the key set exactly when some entry carries it.
proof fn lemma_key_set(entries: Seq<(String, Obj)>, k: Seq<char>)
    ensures
        spec_keys_of(entries).to_set().contains(k) <==> spec_has_key(entries, k),
        spec_objs(entries).dom() == spec_keys_of(entries).to_set(),
{
    broadcast use vstd::seq_lib::group_seq_lib_default;
    let keys = spec_keys_of(entries);
    if spec_has_key(entries, k) {
        let i = spec_index(entries, k);
        assert(keys[i] == k);
        assert(keys.contains(k));
    }
    if keys.to_set().contains(k) {
        let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k;
        assert(entries[i].0@ == k);
    }
}

/// Sorted entries have distinct keys, and each key is found at its index.
proof fn lemma_sorted_index(entries: Seq<(String, Obj)>, i: int)
    requires
        spec_sorted_entries(entries),
        0 <= i < entries.len(),
    ensures
        spec_has_key(entries, entries[i].0@),
        spec_index(entries, entries[i].0@) == i,
        spec_objs(entries).contains_key(entries[i].0@),
        spec_objs(entries)[entries[i].0@] == entries[i].1@,
{
    let k = entries[i].0@;
    assert(spec_has_key(entries, k));
    lemma_key_set(entries, k);
    let j = spec_index(entries, k);
    if j != i {
        if j < i {
            assert(spec_before(entries[j].0@, entries[i].0@));
        } else {
            assert(spec_before(entries[i].0@, entries[j].0@));
        }
        lemma_before_irrefl(k);
    }
}

/// A key the entries have is at some index; one they lack, at none.
proof fn lemma_objs_key(entries: Seq<(String, Obj)>, k: Seq<char>)
    requires
        spec_sorted_entries(entries),
    ensures
        spec_objs(entries).contains_key(k) <==> spec_has_key(entries, k),
        spec_has_key(entries, k) ==> {
            let i = spec_index(entries, k);
            &&& 0 <= i < entries.len()
            &&& entries[i].0@ == k
            &&& spec_objs(entries)[k] == entries[i].1@
        },
{
    lemma_key_set(entries, k);
}

/// The domain of the map is the set of keys, and the keys, sorted, are the keys.
proof fn lemma_sorted_keys(entries: Seq<(String, Obj)>)
    requires
        spec_sorted_entries(entries),
    ensures
        spec_objs(entries).dom() == spec_keys_of(entries).to_set(),
        spec_keys_of(entries).to_set().len() == entries.len(),
        spec_sorted(spec_keys_of(entries).to_set()) == spec_keys_of(entries),
    decreases entries.len(),
{
    broadcast use vstd::seq_lib::group_seq_lib_default;
    let keys = spec_keys_of(entries);
    let set = keys.to_set();
    if entries.len() == 0 {
        assert(set =~= Set::<Seq<char>>::empty());
    } else {
        let rest = entries.drop_first();
        let rest_keys = spec_keys_of(rest);
        assert(rest_keys =~= keys.drop_first());
        assert forall|i: int, j: int| 0 <= i < j < rest.len() implies spec_before(#[trigger] rest[i].0@, #[trigger] rest[j].0@) by {
            assert(rest[i] == entries[i + 1]);
            assert(rest[j] == entries[j + 1]);
        };
        lemma_sorted_keys(rest);
        let first = keys[0];
        assert(set.contains(first));
        // The least key is the first.
        reveal(spec_min_key);
        assert forall|o: Seq<char>| set.contains(o) implies !spec_before(o, first) by {
            let i = choose|i: int| 0 <= i < keys.len() && keys[i] == o;
            if i == 0 {
                lemma_before_irrefl(first);
            } else {
                assert(spec_before(entries[0].0@, entries[i].0@));
                lemma_before_asym(first, o);
            }
        };
        let m = spec_min_key(set);
        assert(set.contains(m) && forall|o: Seq<char>| set.contains(o) ==> !spec_before(o, m));
        if m != first {
            let i = choose|i: int| 0 <= i < keys.len() && keys[i] == m;
            if i == 0 {
                assert(false);
            } else {
                assert(spec_before(entries[0].0@, entries[i].0@));
            }
        }
        assert(m == first);
        assert forall|k: Seq<char>| set.remove(first).contains(k) <==> rest_keys.to_set().contains(k) by {
            if set.remove(first).contains(k) {
                let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k;
                assert(i != 0);
                assert(rest_keys[i - 1] == k);
            }
            if rest_keys.to_set().contains(k) {
                let i = choose|i: int| 0 <= i < rest_keys.len() && rest_keys[i] == k;
                assert(keys[i + 1] == k);
                if k == first {
                    assert(spec_before(entries[0].0@, entries[i + 1].0@));
                    lemma_before_irrefl(first);
                }
            }
        };
        assert(set.remove(first) =~= rest_keys.to_set());
        assert(spec_sorted(set) == seq![first] + spec_sorted(set.remove(first)));
        assert(keys =~= seq![first] + keys.drop_first());
    }
}

/// Two sorted tables are one map exactly when they are the same entries, view for view.
proof fn lemma_objs_eq(a: Seq<(String, Obj)>, b: Seq<(String, Obj)>)
    requires
        spec_sorted_entries(a),
        spec_sorted_entries(b),
    ensures
        (spec_objs(a) == spec_objs(b)) <==> (a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).0@ == b[i].0@ && a[i].1@ == b[i].1@),
{
    lemma_sorted_keys(a);
    lemma_sorted_keys(b);
    if spec_objs(a) == spec_objs(b) {
        assert(spec_keys_of(a) == spec_keys_of(b));
        assert(a.len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i].0@ == b[i].0@ && a[i].1@ == b[i].1@ by {
            assert(spec_keys_of(a)[i] == a[i].0@);
            assert(spec_keys_of(b)[i] == b[i].0@);
            lemma_sorted_index(a, i);
            lemma_sorted_index(b, i);
        };
    }
    if a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].0@ == b[i].0@ && a[i].1@ == b[i].1@ {
        assert forall|k: Seq<char>| spec_objs(a).dom().contains(k) <==> spec_objs(b).dom().contains(k) by {
            lemma_key_set(a, k);
            lemma_key_set(b, k);
            if spec_has_key(a, k) {
                let i = spec_index(a, k);
                assert(b[i].0@ == k);
            }
            if spec_has_key(b, k) {
                let i = spec_index(b, k);
                assert(a[i].0@ == k);
            }
        };
        assert forall|k: Seq<char>| spec_objs(a).dom().contains(k) implies spec_objs(a)[k] == spec_objs(b)[k] by {
            lemma_key_set(a, k);
            let i = spec_index(a, k);
            lemma_sorted_index(a, i);
            lemma_sorted_index(b, i);
        };
        assert(spec_objs(a) =~= spec_objs(b));
    }
}

// ---------------------------------------------------------------------------
// Strings and bytes
// ---------------------------------------------------------------------------

/// A string's characters. Trusted: the view of a `String` is its characters.
#[verifier::external_body]
fn chars_of(text: &String) -> (r: Vec<char>)
    ensures
        r@ == text@,
{
    text.chars().collect()
}

/// `spec_before`: the order the keys are kept in.
fn before(a: &String, b: &String) -> (r: bool)
    ensures
        r == spec_before(a@, b@),
{
    let ac = chars_of(a);
    let bc = chars_of(b);
    let mut i = 0;
    proof {
        assert(a@.skip(0) =~= a@);
        assert(b@.skip(0) =~= b@);
    }
    while i < ac.len() && i < bc.len()
        invariant
            i <= ac.len(),
            i <= bc.len(),
            ac@ == a@,
            bc@ == b@,
            spec_before(a@, b@) == spec_before(a@.skip(i as int), b@.skip(i as int)),
        decreases ac.len() - i,
    {
        if ac[i] != bc[i] {
            return ac[i] < bc[i];
        }
        proof {
            assert(a@.skip(i as int).drop_first() =~= a@.skip(i + 1));
            assert(b@.skip(i as int).drop_first() =~= b@.skip(i + 1));
        }
        i += 1;
    }
    ac.len() < bc.len()
}

/// `spec_starts(key, "s/")`: a schedule document's key.
fn is_schedule_key(key: &String) -> (r: bool)
    ensures
        r == spec_starts(key@, seq!['s', '/']),
{
    let kc = chars_of(key);
    let r = kc.len() >= 2 && kc[0] == 's' && kc[1] == '/';
    proof {
        reveal_with_fuel(spec_starts, 3);
        let p = seq!['s', '/'];
        assert(p.drop_first() =~= seq!['/']);
        assert(seq!['/'].drop_first() =~= Seq::<char>::empty());
        if key@.len() >= 1 {
            assert(key@.drop_first().len() == key@.len() - 1);
            if key@.len() >= 2 {
                assert(key@.drop_first()[0] == key@[1]);
            }
        }
    }
    r
}

/// A string from a literal, as the spec names it.
fn string_lit(text: &str) -> (r: String)
    ensures
        r@ == text@,
{
    text.to_owned()
}

/// `spec_origin_key(origin(id))`.
fn origin_key(id: &String) -> (r: String)
    ensures
        r@ == spec_origin_key(origin(id@)),
{
    let mut s = String::new();
    s.push('o');
    s.push('/');
    s.push_str(origin_of(id.as_str()));
    proof {
        assert(s@ =~= seq!['o', '/'] + origin(id@));
    }
    s
}

/// `spec_schedule_key(id)`.
fn schedule_key(id: &String) -> (r: String)
    ensures
        r@ == spec_schedule_key(id@),
{
    let mut s = String::new();
    s.push('s');
    s.push('/');
    s.push_str(id.as_str());
    proof {
        assert(s@ =~= seq!['s', '/'] + id@);
    }
    s
}

fn same_strs(a: &Vec<String>, b: &Vec<String>) -> (r: bool)
    ensures
        r == (strs_v(a@) == strs_v(b@)),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> strs_v(a@)[j] == strs_v(b@)[j],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            assert(strs_v(a@)[i as int] != strs_v(b@)[i as int]);
            return false;
        }
        i += 1;
    }
    proof {
        assert(strs_v(a@) =~= strs_v(b@));
    }
    true
}

fn contains_str(ids: &Vec<String>, id: &String) -> (r: bool)
    ensures
        r == strs_v(ids@).contains(id@),
{
    let mut i = 0;
    while i < ids.len()
        invariant
            i <= ids.len(),
            forall|j: int| 0 <= j < i ==> strs_v(ids@)[j] != id@,
        decreases ids.len() - i,
    {
        if ids[i] == *id {
            assert(strs_v(ids@)[i as int] == id@);
            return true;
        }
        i += 1;
    }
    false
}

fn same_tags(a: &Tags, b: &Tags) -> (r: bool)
    ensures
        r == (*a == *b),
{
    if a.len() != b.len() {
        assert(a@ != b@);
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> a.deep_view()[j] == b.deep_view()[j],
        decreases a.len() - i,
    {
        if a[i].0 != b[i].0 || a[i].1 != b[i].1 {
            assert(a@[i as int] != b@[i as int]);
            assert(a@ != b@);
            return false;
        }
        assert(a.deep_view()[i as int] == b.deep_view()[i as int]);
        i += 1;
    }
    proof {
        assert(a.deep_view() =~= b.deep_view());
        lemma_tags_ext(*a, *b);
    }
    true
}

fn same_value(a: &Value, b: &Value) -> (r: bool)
    ensures
        r == (*a == *b),
{
    if !same_tags(&a.headers, &b.headers) {
        return false;
    }
    match (&a.data, &b.data) {
        (Some(x), Some(y)) => {
            if *x == *y {
                proof {
                    axiom_string_ext(*x, *y);
                }
                true
            } else {
                false
            }
        },
        (None, None) => true,
        _ => false,
    }
}

fn same_opt_u64(a: &Option<u64>, b: &Option<u64>) -> (r: bool)
    ensures
        r == (*a == *b),
{
    match (a, b) {
        (Some(x), Some(y)) => *x == *y,
        (None, None) => true,
        _ => false,
    }
}

fn same_opt_str(a: &Option<String>, b: &Option<String>) -> (r: bool)
    ensures
        r == (match (*a, *b) { (Some(x), Some(y)) => x@ == y@, (None, None) => true, _ => false }),
{
    match (a, b) {
        (Some(x), Some(y)) => *x == *y,
        (None, None) => true,
        _ => false,
    }
}

fn same_prom(a: &Prom, b: &Prom) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    a.state == b.state
        && same_value(&a.param, &b.param)
        && same_value(&a.value, &b.value)
        && same_tags(&a.tags, &b.tags)
        && a.timeout_at == b.timeout_at
        && a.created_at == b.created_at
        && same_opt_u64(&a.settled_at, &b.settled_at)
        && same_strs(&a.callbacks, &b.callbacks)
        && same_strs(&a.listeners, &b.listeners)
}

fn same_tk(a: &Tk, b: &Tk) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    a.state == b.state
        && a.version == b.version
        && same_opt_str(&a.pid, &b.pid)
        && same_opt_u64(&a.ttl, &b.ttl)
        && same_opt_u64(&a.lease_timeout_at, &b.lease_timeout_at)
        && same_opt_u64(&a.retry_timeout_at, &b.retry_timeout_at)
        && same_strs(&a.resumes, &b.resumes)
}

fn same_obj(a: &Obj, b: &Obj) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if !same_prom(&a.promise, &b.promise) {
        return false;
    }
    match (&a.task, &b.task) {
        (Some(x), Some(y)) => same_tk(x, y),
        (None, None) => true,
        _ => false,
    }
}

fn same_objects(a: &Objects, b: &Objects) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    proof {
        use_type_invariant(a);
        use_type_invariant(b);
        lemma_objs_eq(a.entries@, b.entries@);
    }
    if a.entries.len() != b.entries.len() {
        return false;
    }
    let mut i = 0;
    while i < a.entries.len()
        invariant
            i <= a.entries.len(),
            a.entries.len() == b.entries.len(),
            forall|j: int| 0 <= j < i ==> (#[trigger] a.entries@[j]).0@ == b.entries@[j].0@ && a.entries@[j].1@ == b.entries@[j].1@,
            (a@ == b@) <==> forall|j: int| 0 <= j < a.entries@.len() ==> (#[trigger] a.entries@[j]).0@ == b.entries@[j].0@ && a.entries@[j].1@ == b.entries@[j].1@,
        decreases a.entries.len() - i,
    {
        if !(a.entries[i].0 == b.entries[i].0) || !same_obj(&a.entries[i].1, &b.entries[i].1) {
            return false;
        }
        assert(a.entries@[i as int].0@ == b.entries@[i as int].0@);
        assert(a.entries@[i as int].1@ == b.entries@[i as int].1@);
        i += 1;
    }
    true
}

fn same_schedule(a: &Schedule, b: &Schedule) -> (r: bool)
    ensures
        r == (*a == *b),
{
    if a.id == b.id
        && a.cron == b.cron
        && a.promise_id == b.promise_id
        && a.promise_timeout == b.promise_timeout
        && same_value(&a.promise_param, &b.promise_param)
        && same_tags(&a.promise_tags, &b.promise_tags)
        && a.next_run_at == b.next_run_at
        && same_opt_u64(&a.last_run_at, &b.last_run_at)
        && a.created_at == b.created_at
    {
        proof {
            axiom_string_ext(a.id, b.id);
            axiom_string_ext(a.cron, b.cron);
            axiom_string_ext(a.promise_id, b.promise_id);
        }
        true
    } else {
        false
    }
}

/// `next == previous`, on documents.
pub fn same_body(a: &DocumentBody, b: &DocumentBody) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    match (a, b) {
        (DocumentBody::Workflow(x), DocumentBody::Workflow(y)) => same_objects(x, y),
        (DocumentBody::Schedule(Some(x)), DocumentBody::Schedule(Some(y))) => same_schedule(x, y),
        (DocumentBody::Schedule(None), DocumentBody::Schedule(None)) => true,
        _ => false,
    }
}

/// A copy of a document, equal to its source.
pub fn clone_body(d: &DocumentBody) -> (r: DocumentBody)
    ensures
        r == *d,
{
    match d {
        DocumentBody::Workflow(objs) => DocumentBody::Workflow(objs.clone()),
        DocumentBody::Schedule(slot) => DocumentBody::Schedule(echod_abstract::trusted::copy(slot)),
    }
}

pub open spec fn spec_stored_body(d: StoredDocumentV) -> DocumentBodyV {
    match d {
        StoredDocumentV::Workflow(doc) => DocumentBodyV::Workflow(doc.objects),
        StoredDocumentV::Schedule(doc) => DocumentBodyV::Schedule(doc.schedule),
    }
}

pub fn stored_body(d: &StoredDocument) -> (r: DocumentBody)
    ensures
        r@ == spec_stored_body(d@),
{
    match d {
        StoredDocument::Workflow(doc) => DocumentBody::Workflow(doc.objects.clone()),
        StoredDocument::Schedule(doc) => DocumentBody::Schedule(copy(&doc.schedule)),
    }
}

pub fn clone_stored(d: &StoredDocument) -> (r: StoredDocument)
    ensures r == *d,
{
    match d {
        StoredDocument::Workflow(doc) => StoredDocument::Workflow(WorkflowDocument {
            document: doc.document.clone(),
            version: doc.version,
            committed_at: doc.committed_at,
            next_wake_at: doc.next_wake_at,
            objects: doc.objects.clone(),
        }),
        StoredDocument::Schedule(doc) => StoredDocument::Schedule(ScheduleDocument {
            document: doc.document.clone(),
            version: doc.version,
            committed_at: doc.committed_at,
            next_wake_at: doc.next_wake_at,
            schedule: copy(&doc.schedule),
        }),
    }
}

pub open spec fn spec_stored_version(d: StoredDocumentV) -> u64 {
    match d {
        StoredDocumentV::Workflow(doc) => doc.version,
        StoredDocumentV::Schedule(doc) => doc.version,
    }
}

pub open spec fn spec_stored_committed_at(d: StoredDocumentV) -> u64 {
    match d {
        StoredDocumentV::Workflow(doc) => doc.committed_at,
        StoredDocumentV::Schedule(doc) => doc.committed_at,
    }
}

pub open spec fn spec_stored_next_wake_at(d: StoredDocumentV) -> Option<u64> {
    match d {
        StoredDocumentV::Workflow(doc) => doc.next_wake_at,
        StoredDocumentV::Schedule(doc) => doc.next_wake_at,
    }
}

pub open spec fn spec_stored_name(d: StoredDocumentV) -> Seq<char> {
    match d {
        StoredDocumentV::Workflow(doc) => doc.document,
        StoredDocumentV::Schedule(doc) => doc.document,
    }
}

pub fn stored_version(d: &StoredDocument) -> (r: u64)
    ensures r == spec_stored_version(d@),
{
    match d {
        StoredDocument::Workflow(doc) => doc.version,
        StoredDocument::Schedule(doc) => doc.version,
    }
}

pub fn stored_committed_at(d: &StoredDocument) -> (r: u64)
    ensures r == spec_stored_committed_at(d@),
{
    match d {
        StoredDocument::Workflow(doc) => doc.committed_at,
        StoredDocument::Schedule(doc) => doc.committed_at,
    }
}

pub fn stored_next_wake_at(d: &StoredDocument) -> (r: Option<u64>)
    ensures r == spec_stored_next_wake_at(d@),
{
    match d {
        StoredDocument::Workflow(doc) => doc.next_wake_at,
        StoredDocument::Schedule(doc) => doc.next_wake_at,
    }
}

pub fn stored_is_workflow(d: &StoredDocument) -> (r: bool)
    ensures r == (d@ is Workflow),
{
    match d {
        StoredDocument::Workflow(_) => true,
        StoredDocument::Schedule(_) => false,
    }
}

pub open spec fn spec_empty_stored_workflow(document: Seq<char>) -> StoredDocumentV {
    StoredDocumentV::Workflow(WorkflowDocumentV {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        objects: Map::empty(),
    })
}

pub open spec fn spec_empty_stored_schedule(document: Seq<char>) -> StoredDocumentV {
    StoredDocumentV::Schedule(ScheduleDocumentV {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        schedule: None,
    })
}

pub fn empty_stored_workflow(document: String) -> (r: StoredDocument)
    ensures r@ == spec_empty_stored_workflow(document@),
{
    StoredDocument::Workflow(WorkflowDocument {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        objects: Objects::empty(),
    })
}

pub fn empty_stored_schedule(document: String) -> (r: StoredDocument)
    ensures r@ == spec_empty_stored_schedule(document@),
{
    StoredDocument::Schedule(ScheduleDocument {
        document,
        version: 0,
        committed_at: 0,
        next_wake_at: None,
        schedule: None,
    })
}

pub open spec fn spec_advance_stored(
    before: StoredDocumentV,
    body: DocumentBodyV,
    committed_at: u64,
) -> StoredDocumentV {
    let version = spec_stored_version(before).saturating_add(1);
    let next_wake_at = match spec_body_deadline(body) {
        Some(at) => Some(at as u64),
        None => None,
    };
    match body {
        DocumentBodyV::Workflow(objects) => StoredDocumentV::Workflow(WorkflowDocumentV {
            document: spec_stored_name(before),
            version,
            committed_at,
            next_wake_at,
            objects,
        }),
        DocumentBodyV::Schedule(schedule) => StoredDocumentV::Schedule(ScheduleDocumentV {
            document: spec_stored_name(before),
            version,
            committed_at,
            next_wake_at,
            schedule,
        }),
    }
}

pub fn advance_stored(
    before: &StoredDocument,
    body: DocumentBody,
    committed_at: u64,
) -> (r: StoredDocument)
    ensures r@ == spec_advance_stored(before@, body@, committed_at),
{
    let document = match before {
        StoredDocument::Workflow(doc) => doc.document.clone(),
        StoredDocument::Schedule(doc) => doc.document.clone(),
    };
    let version = stored_version(before).saturating_add(1);
    let next_wake_at = body_deadline(&body);
    match body {
        DocumentBody::Workflow(objects) => StoredDocument::Workflow(WorkflowDocument {
            document,
            version,
            committed_at,
            next_wake_at,
            objects,
        }),
        DocumentBody::Schedule(schedule) => StoredDocument::Schedule(ScheduleDocument {
            document,
            version,
            committed_at,
            next_wake_at,
            schedule,
        }),
    }
}

impl LoadedDocument {
    pub fn empty_workflow(document: String) -> (r: LoadedDocument)
        ensures
            r@ == (LoadedDocumentV {
                document: spec_empty_stored_workflow(document@),
                change_count: 0,
                bytes: 0,
                append_certified: false,
            }),
    {
        LoadedDocument {
            document: empty_stored_workflow(document),
            change_count: 0,
            bytes: 0,
            append_certified: false,
        }
    }

    pub fn empty_schedule(document: String) -> (r: LoadedDocument)
        ensures
            r@ == (LoadedDocumentV {
                document: spec_empty_stored_schedule(document@),
                change_count: 0,
                bytes: 0,
                append_certified: false,
            }),
    {
        LoadedDocument {
            document: empty_stored_schedule(document),
            change_count: 0,
            bytes: 0,
            append_certified: false,
        }
    }

    pub fn copy(&self) -> (r: LoadedDocument)
        ensures r == *self,
    {
        LoadedDocument {
            document: clone_stored(&self.document),
            change_count: self.change_count,
            bytes: self.bytes,
            append_certified: self.append_certified,
        }
    }
}

/// What a document's view is, variant by variant, for code outside this
/// crate that matches on a `DocumentBody`.
pub proof fn lemma_doc_view(d: &DocumentBody)
    ensures
        d@ == match d {
            DocumentBody::Workflow(objs) => DocumentBodyV::Workflow(objs@),
            DocumentBody::Schedule(slot) => DocumentBodyV::Schedule(*slot),
        },
{
}

/// What a stored document's view is, variant by variant, for verified
/// process code that validates the loaded family before using it.
pub proof fn lemma_stored_document_view(d: &StoredDocument)
    ensures
        d@ == match d {
            StoredDocument::Workflow(document) =>
                StoredDocumentV::Workflow(document@),
            StoredDocument::Schedule(document) =>
                StoredDocumentV::Schedule(document@),
        },
{
}

/// The family and stored name exposed by a stored document's view.
pub proof fn lemma_stored_document_identity_view(d: &StoredDocument)
    ensures
        match d {
            StoredDocument::Workflow(document) => {
                &&& d@ is Workflow
                &&& d@->Workflow_0.document == document.document@
            },
            StoredDocument::Schedule(document) => {
                &&& d@ is Schedule
                &&& d@->Schedule_0.document == document.document@
            },
        },
{
}

/// What an object's view says of its tags and its task, for code outside
/// this crate that reads an object it peeked.
pub proof fn lemma_obj_view(o: &Obj)
    ensures
        o@.promise.tags == o.promise.tags,
        (o@.task is Some) == (o.task is Some),
        o.task is Some ==> o@.task->Some_0.state == o.task->Some_0.state,
{
}

/// How many rows a document holds: its objects, or its one schedule.
pub open spec fn spec_body_len(d: DocumentBodyV) -> nat {
    match d {
        DocumentBodyV::Workflow(m) => m.dom().len(),
        DocumentBodyV::Schedule(Some(_)) => 1,
        DocumentBodyV::Schedule(None) => 0,
    }
}

pub fn body_len(d: &DocumentBody) -> (r: usize)
    ensures
        r as nat == spec_body_len(d@),
{
    match d {
        DocumentBody::Workflow(objs) => {
            proof {
                use_type_invariant(objs);
                lemma_sorted_keys(objs.entries@);
            }
            objs.entries.len()
        },
        DocumentBody::Schedule(Some(_)) => 1,
        DocumentBody::Schedule(None) => 0,
    }
}

/// What a note's view is, variant by variant.
pub proof fn lemma_outbound_view(n: &Outbound)
    ensures
        n@ == match n {
            Outbound::Execute { id, version } => NoteV::Execute { id: id@, version: *version },
            Outbound::Unblock { address, promise } => NoteV::Unblock { address: address@, promise: *promise },
        },
{
}

/// What an occurrence's view is, field by field.
pub proof fn lemma_pending_view(p: &Pending)
    ensures
        p@ == (PendingV { promise: p.promise@, at: p.at, timeout: p.timeout, param: p.param, tags: p.tags }),
{
}

/// An workflow's empty document.
pub fn empty_workflow() -> (r: DocumentBody)
    ensures
        r@ == DocumentBodyV::Workflow(Map::<Seq<char>, ObjV>::empty()),
{
    DocumentBody::Workflow(Objects::empty())
}

/// A schedule's empty document.
pub fn empty_schedule() -> (r: DocumentBody)
    ensures
        r@ == DocumentBodyV::Schedule(None),
{
    DocumentBody::Schedule(None)
}

/// Every id of `a` is an id of `b`: nothing was removed between them.
pub fn keys_within(a: &Objects, b: &Objects) -> (r: bool)
    ensures
        r == a@.dom().subset_of(b@.dom()),
{
    proof {
        use_type_invariant(a);
    }
    let mut i = 0;
    while i < a.entries.len()
        invariant
            i <= a.entries.len(),
            forall|j: int| 0 <= j < i ==> b@.contains_key(#[trigger] a.entries@[j].0@),
        decreases a.entries.len() - i,
    {
        if !b.contains(&a.entries[i].0) {
            proof {
                lemma_key_set(a.entries@, a.entries@[i as int].0@);
                assert(spec_has_key(a.entries@, a.entries@[i as int].0@));
                assert(a@.contains_key(a.entries@[i as int].0@));
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert forall|k: Seq<char>| a@.dom().contains(k) implies b@.dom().contains(k) by {
            lemma_key_set(a.entries@, k);
            let j = spec_index(a.entries@, k);
            assert(a.entries@[j].0@ == k);
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Tags
// ---------------------------------------------------------------------------

fn tag_is(tags: &Tags, key: &str, value: &str) -> (r: bool)
    ensures
        r == spec_tag_is(*tags, key@, value@, 0),
{
    let mut i: usize = 0;
    while i < tags.len()
        invariant
            i <= tags.len(),
            spec_tag_is(*tags, key@, value@, 0) == spec_tag_is(*tags, key@, value@, i as int),
        decreases tags.len() - i,
    {
        if tags[i].0.as_str() == key {
            return tags[i].1.as_str() == value;
        }
        i += 1;
    }
    false
}

fn tag_key(tags: &Tags, key: &str) -> (r: bool)
    ensures
        r == spec_tag_key(*tags, key@, 0),
{
    let mut i: usize = 0;
    while i < tags.len()
        invariant
            i <= tags.len(),
            spec_tag_key(*tags, key@, 0) == spec_tag_key(*tags, key@, i as int),
        decreases tags.len() - i,
    {
        if tags[i].0.as_str() == key {
            return true;
        }
        i += 1;
    }
    false
}

pub(crate) fn timer(tags: &Tags) -> (r: bool)
    ensures
        r == spec_timer(*tags),
{
    proof {
        reveal_strlit("resonate:timer");
        reveal_strlit("true");
        assert("resonate:timer"@ =~= seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r']);
        assert("true"@ =~= seq!['t','r','u','e']);
    }
    tag_is(tags, "resonate:timer", "true")
}

pub(crate) fn targeted(tags: &Tags) -> (r: bool)
    ensures
        r == spec_targeted(*tags),
{
    proof {
        reveal_strlit("resonate:target");
        assert("resonate:target"@ =~= seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t']);
    }
    tag_key(tags, "resonate:target")
}

/// Lean's `otype.awaitable`: a target, global scope, an external tag, or a timer.
pub(crate) fn awaitable(tags: &Tags) -> (r: bool)
    ensures
        r == spec_awaitable(*tags),
{
    proof {
        reveal_strlit("resonate:external");
        reveal_strlit("resonate:scope");
        reveal_strlit("global");
        reveal_strlit("true");
        assert("resonate:external"@ =~= seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l']);
        assert("resonate:scope"@ =~= seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e']);
        assert("global"@ =~= seq!['g','l','o','b','a','l']);
        assert("true"@ =~= seq!['t','r','u','e']);
    }
    targeted(tags)
        || timer(tags)
        || tag_is(tags, "resonate:external", "true")
        || tag_is(tags, "resonate:scope", "global")
}

/// Decimal digits to a number, `None` on anything else or on overflow:
/// `spec_parse_u64`, what `str::parse::<u64>` accepts.
fn parse_u64(text: &String) -> (r: Option<u64>)
    ensures
        r == spec_parse_u64(text@),
{
    let chars = chars_of(text);
    if chars.len() == 0 {
        return None;
    }
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            i <= chars.len(),
            chars@ == text@,
            text@.len() > 0,
            spec_parse_u64(text@) == spec_parse_acc(text@, i as int, acc as nat),
        decreases chars.len() - i,
    {
        let c = chars[i];
        if c < '0' || c > '9' {
            return None;
        }
        let d = (c as u64) - ('0' as u64);
        if acc > (u64::MAX - d) / 10 {
            proof {
                assert((acc as nat) * 10 + (d as nat) > u64::MAX as nat) by (nonlinear_arith)
                    requires acc > (u64::MAX - d) / 10, d <= 9;
            }
            return None;
        }
        proof {
            assert((acc as nat) * 10 + (d as nat) <= u64::MAX as nat) by (nonlinear_arith)
                requires acc <= (u64::MAX - d) / 10, d <= 9;
        }
        acc = acc * 10 + d;
        i += 1;
    }
    Some(acc)
}

/// `spec_delay(tags, 0)`.
fn delay_of(tags: &Tags) -> (r: Option<u64>)
    ensures
        r == spec_delay(*tags, 0),
{
    proof {
        reveal_strlit("resonate:delay");
        assert("resonate:delay"@ =~= seq!['r','e','s','o','n','a','t','e',':','d','e','l','a','y']);
    }
    let mut i: usize = 0;
    while i < tags.len()
        invariant
            i <= tags.len(),
            spec_delay(*tags, 0) == spec_delay(*tags, i as int),
        decreases tags.len() - i,
    {
        proof {
            reveal_strlit("resonate:delay");
            assert("resonate:delay"@ =~= seq!['r','e','s','o','n','a','t','e',':','d','e','l','a','y']);
        }
        if tags[i].0.as_str() == "resonate:delay" {
            return parse_u64(&tags[i].1);
        }
        i += 1;
    }
    None
}

/// The first offer of a task born at `at`: `spec_offer_at`.
fn offer_at(tags: &Tags, at: u64) -> (r: u64)
    ensures
        r == spec_offer_at(*tags, at),
{
    match delay_of(tags) {
        Some(d) => if d > at { d } else { at },
        None => at,
    }
}

/// `spec_sat_add`.
fn sat_add(a: u64, b: u64) -> (r: u64)
    ensures
        r == spec_sat_add(a, b),
{
    a.saturating_add(b)
}


// ---------------------------------------------------------------------------
// Lists of ids
// ---------------------------------------------------------------------------

proof fn lemma_strs_empty()
    ensures
        strs_v(Seq::<String>::empty()) == Seq::<Seq<char>>::empty(),
{
    assert(strs_v(Seq::<String>::empty()) =~= Seq::<Seq<char>>::empty());
}

proof fn lemma_strs_push(v: Seq<String>, s: String)
    ensures
        strs_v(v.push(s)) == strs_v(v).push(s@),
{
    assert(strs_v(v.push(s)) =~= strs_v(v).push(s@));
}

proof fn lemma_strs_skip(v: Seq<String>)
    requires
        v.len() > 0,
    ensures
        strs_v(v.remove(0)) == strs_v(v).skip(1),
{
    assert(strs_v(v.remove(0)) =~= strs_v(v).skip(1));
}

/// `ids.push(id)`, on the views.
fn push_id(ids: &mut Vec<String>, id: &String)
    ensures
        strs_v(final(ids)@) == strs_v(old(ids)@).push(id@),
{
    let ghost before = ids@;
    ids.push(id.clone());
    proof {
        lemma_strs_push(before, ids@[ids@.len() - 1]);
    }
}

// ---------------------------------------------------------------------------
// The sorted table
// ---------------------------------------------------------------------------

/// Replacing the object at an index keeps the order and is a map insert.
proof fn lemma_objs_update(entries: Seq<(String, Obj)>, i: int, e: (String, Obj))
    requires
        spec_sorted_entries(entries),
        0 <= i < entries.len(),
        e.0@ == entries[i].0@,
    ensures
        spec_sorted_entries(entries.update(i, e)),
        spec_objs(entries.update(i, e)) == spec_objs(entries).insert(e.0@, e.1@),
{
    let next = entries.update(i, e);
    let target = spec_objs(entries).insert(e.0@, e.1@);
    assert forall|a: int, b: int| 0 <= a < b < next.len() implies spec_before(#[trigger] next[a].0@, #[trigger] next[b].0@) by {
        assert(next[a].0@ == entries[a].0@);
        assert(next[b].0@ == entries[b].0@);
    };
    assert forall|k: Seq<char>| spec_objs(next).dom().contains(k) <==> target.dom().contains(k) by {
        lemma_key_set(next, k);
        lemma_key_set(entries, k);
        if spec_has_key(next, k) {
            let j = spec_index(next, k);
            assert(entries[j].0@ == k);
        }
        if spec_has_key(entries, k) {
            let j = spec_index(entries, k);
            assert(next[j].0@ == k);
        }
    };
    assert forall|k: Seq<char>| spec_objs(next).dom().contains(k) implies spec_objs(next)[k] == target[k] by {
        lemma_key_set(next, k);
        let j = spec_index(next, k);
        lemma_sorted_index(next, j);
        assert(entries[j].0@ == k);
        lemma_sorted_index(entries, j);
        if j != i && k == e.0@ {
            if j < i {
                assert(spec_before(entries[j].0@, entries[i].0@));
            } else {
                assert(spec_before(entries[i].0@, entries[j].0@));
            }
            lemma_before_irrefl(k);
        }
    };
    assert(spec_objs(next) =~= target);
}

/// Inserting at the key's place keeps the order and is a map insert.
proof fn lemma_objs_insert(entries: Seq<(String, Obj)>, i: int, e: (String, Obj))
    requires
        spec_sorted_entries(entries),
        0 <= i <= entries.len(),
        forall|j: int| 0 <= j < i ==> spec_before(#[trigger] entries[j].0@, e.0@),
        forall|j: int| i <= j < entries.len() ==> spec_before(e.0@, #[trigger] entries[j].0@),
    ensures
        spec_sorted_entries(entries.insert(i, e)),
        spec_objs(entries.insert(i, e)) == spec_objs(entries).insert(e.0@, e.1@),
{
    let next = entries.insert(i, e);
    let target = spec_objs(entries).insert(e.0@, e.1@);
    assert(next.len() == entries.len() + 1);
    assert forall|j: int| 0 <= j < i implies #[trigger] next[j] == entries[j] by {};
    assert(next[i] == e);
    assert forall|j: int| i < j < next.len() implies #[trigger] next[j] == entries[j - 1] by {};
    assert forall|a: int, b: int| 0 <= a < b < next.len() implies spec_before(#[trigger] next[a].0@, #[trigger] next[b].0@) by {
        if a < i {
            if b < i {
            } else if b == i {
            } else {
                assert(next[b] == entries[b - 1]);
                lemma_before_trans(entries[a].0@, e.0@, entries[b - 1].0@);
            }
        } else if a == i {
            assert(next[b] == entries[b - 1]);
        } else {
            assert(next[a] == entries[a - 1]);
            assert(next[b] == entries[b - 1]);
        }
    };
    assert forall|k: Seq<char>| spec_objs(next).dom().contains(k) <==> target.dom().contains(k) by {
        lemma_key_set(next, k);
        lemma_key_set(entries, k);
        if spec_has_key(next, k) {
            let j = spec_index(next, k);
            if j < i {
                assert(entries[j].0@ == k);
            } else if j > i {
                assert(entries[j - 1].0@ == k);
            }
        }
        if spec_has_key(entries, k) {
            let j = spec_index(entries, k);
            if j < i {
                assert(next[j].0@ == k);
            } else {
                assert(next[j + 1].0@ == k);
            }
        }
    };
    assert forall|k: Seq<char>| spec_objs(next).dom().contains(k) implies spec_objs(next)[k] == target[k] by {
        lemma_key_set(next, k);
        let j = spec_index(next, k);
        lemma_sorted_index(next, j);
        if j == i {
        } else if j < i {
            assert(entries[j].0@ == k);
            lemma_sorted_index(entries, j);
            if k == e.0@ {
                lemma_before_irrefl(k);
            }
        } else {
            assert(entries[j - 1].0@ == k);
            lemma_sorted_index(entries, j - 1);
            if k == e.0@ {
                lemma_before_irrefl(k);
            }
        }
    };
    assert(spec_objs(next) =~= target);
}

/// The index of an id, if the table has it.
fn find_id(entries: &Vec<(String, Obj)>, id: &String) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < entries.len() && entries@[i as int].0@ == id@,
            None => !spec_has_key(entries@, id@),
        },
{
    let mut i: usize = 0;
    while i < entries.len()
        invariant
            i <= entries.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] entries@[j].0@ != id@,
        decreases entries.len() - i,
    {
        if entries[i].0 == *id {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Where a new id goes: before the first key it is before.
fn insert_at(entries: &Vec<(String, Obj)>, id: &String) -> (i: usize)
    requires
        spec_sorted_entries(entries@),
        !spec_has_key(entries@, id@),
    ensures
        i <= entries.len(),
        forall|j: int| 0 <= j < i ==> spec_before(#[trigger] entries@[j].0@, id@),
        forall|j: int| i <= j < entries.len() ==> spec_before(id@, #[trigger] entries@[j].0@),
{
    let mut i: usize = 0;
    while i < entries.len()
        invariant
            i <= entries.len(),
            spec_sorted_entries(entries@),
            !spec_has_key(entries@, id@),
            forall|j: int| 0 <= j < i ==> spec_before(#[trigger] entries@[j].0@, id@),
        decreases entries.len() - i,
    {
        if !before(&entries[i].0, id) {
            proof {
                assert(entries@[i as int].0@ != id@);
                lemma_before_total(entries@[i as int].0@, id@);
                assert forall|j: int| i <= j < entries.len() implies spec_before(id@, #[trigger] entries@[j].0@) by {
                    if j > i {
                        lemma_before_trans(id@, entries@[i as int].0@, entries@[j].0@);
                    }
                };
            }
            return i;
        }
        i += 1;
    }
    i
}

impl Objects {
    pub fn empty() -> (r: Objects)
        ensures
            r@ == Map::<Seq<char>, ObjV>::empty(),
    {
        let r = Objects { entries: Vec::new() };
        proof {
            broadcast use vstd::seq_lib::group_seq_lib_default;
            assert(spec_keys_of(r.entries@) =~= Seq::<Seq<char>>::empty());
            assert(spec_keys_of(r.entries@).to_set() =~= Set::<Seq<char>>::empty());
            assert(r@ =~= Map::<Seq<char>, ObjV>::empty());
        }
        r
    }

    /// `map[id]`, copied out.
    pub fn get(&self, id: &String) -> (r: Option<Obj>)
        ensures
            match r {
                Some(o) => self@.contains_key(id@) && o@ == self@[id@],
                None => !self@.contains_key(id@),
            },
    {
        proof {
            use_type_invariant(self);
        }
        match find_id(&self.entries, id) {
            Some(i) => {
                proof {
                    lemma_sorted_index(self.entries@, i as int);
                }
                Some(copy(&self.entries[i].1))
            },
            None => {
                proof {
                    lemma_key_set(self.entries@, id@);
                }
                None
            },
        }
    }

    fn contains(&self, id: &String) -> (r: bool)
        ensures
            r == self@.contains_key(id@),
    {
        proof {
            use_type_invariant(self);
            lemma_key_set(self.entries@, id@);
        }
        match find_id(&self.entries, id) {
            Some(_) => true,
            None => false,
        }
    }

    /// `map.insert(id, obj)`.
    pub fn put(self, id: &String, obj: Obj) -> (r: Objects)
        ensures
            r@ == self@.insert(id@, obj@),
    {
        proof {
            use_type_invariant(&self);
        }
        let Objects { mut entries } = self;
        let ghost before_v = entries@;
        let e = (id.clone(), obj);
        let ghost ev = e;
        match find_id(&entries, id) {
            Some(i) => {
                proof {
                    lemma_objs_update(before_v, i as int, ev);
                }
                entries.set(i, e);
                Objects { entries }
            },
            None => {
                let i = insert_at(&entries, id);
                proof {
                    lemma_objs_insert(before_v, i as int, ev);
                }
                entries.insert(i, e);
                Objects { entries }
            },
        }
    }

    fn is_empty(&self) -> (r: bool)
        ensures
            r == (self@.dom().len() == 0),
    {
        proof {
            use_type_invariant(self);
            lemma_sorted_keys(self.entries@);
        }
        self.entries.len() == 0
    }

    /// The table of `entries`, each put in turn: `spec_from_entries`. A
    /// later entry with an id already seen replaces the earlier one.
    pub fn from_entries(entries: Vec<(String, Obj)>) -> (r: Objects)
        ensures
            r@ == spec_from_entries(entries@),
    {
        let mut objs = Objects::empty();
        let mut i: usize = 0;
        proof {
            lemma_from_entries_prefix(entries@, 0);
        }
        while i < entries.len()
            invariant
                i <= entries@.len(),
                objs@ == spec_from_entries(entries@.take(i as int)),
            decreases entries@.len() - i,
        {
            let (id, obj) = copy(&entries[i]);
            objs = objs.put(&id, obj);
            proof {
                lemma_from_entries_step(entries@, i as int);
            }
            i += 1;
        }
        proof {
            assert(entries@.take(entries@.len() as int) =~= entries@);
        }
        objs
    }

    /// The entries, in key order: the table as a map, entry by entry.
    pub fn into_entries(self) -> (r: Vec<(String, Obj)>)
        ensures
            spec_from_entries(r@) == self@,
            spec_sorted_entries(r@),
            spec_keys_of(r@) == spec_sorted_present(self@),
            forall|i: int| 0 <= i < r.len() ==>
                self@.contains_key(#[trigger] r[i].0@),
    {
        proof {
            use_type_invariant(&self);
            lemma_from_entries_sorted(self.entries@);
            lemma_sorted_keys(self.entries@);
            assert forall|i: int| 0 <= i < self.entries@.len() implies
                self@.contains_key(#[trigger] self.entries@[i].0@) by {
                lemma_sorted_index(self.entries@, i);
            };
        }
        self.entries
    }

    /// `spec_map_deadline` over the keys in order.
    pub(crate) fn deadline(&self) -> (r: Option<u64>)
        ensures
            nat_v(r) == spec_map_deadline(self@, spec_sorted(self@.dom())),
    {
        proof {
            use_type_invariant(self);
            lemma_sorted_keys(self.entries@);
        }
        let ghost map = self@;
        let ghost keys = spec_keys_of(self.entries@);
        let mut i: usize = self.entries.len();
        let mut acc: Option<u64> = None;
        proof {
            assert(keys.skip(i as int).len() == 0);
        }
        while i > 0
            invariant
                i <= self.entries.len(),
                map == self@,
                keys == spec_keys_of(self.entries@),
                spec_sorted_entries(self.entries@),
                nat_v(acc) == spec_map_deadline(map, keys.skip(i as int)),
            decreases i,
        {
            i -= 1;
            proof {
                lemma_sorted_index(self.entries@, i as int);
                assert(keys.skip(i as int)[0] == self.entries@[i as int].0@);
                assert(keys.skip(i as int).drop_first() =~= keys.skip(i + 1));
            }
            acc = min_u64(obj_deadline(&self.entries[i].1), acc);
        }
        proof {
            assert(keys.skip(0) =~= keys);
        }
        acc
    }

    /// `spec_map_due` over the keys in order.
    fn earliest(&self, now: u64) -> (r: Option<u64>)
        ensures
            r == spec_map_due(self@, spec_sorted(self@.dom()), now),
    {
        proof {
            use_type_invariant(self);
            lemma_sorted_keys(self.entries@);
        }
        let ghost map = self@;
        let ghost keys = spec_keys_of(self.entries@);
        let mut i: usize = self.entries.len();
        let mut acc: Option<u64> = None;
        proof {
            assert(keys.skip(i as int).len() == 0);
        }
        while i > 0
            invariant
                i <= self.entries.len(),
                map == self@,
                keys == spec_keys_of(self.entries@),
                spec_sorted_entries(self.entries@),
                acc == spec_map_due(map, keys.skip(i as int), now),
            decreases i,
        {
            i -= 1;
            proof {
                lemma_sorted_index(self.entries@, i as int);
                assert(keys.skip(i as int)[0] == self.entries@[i as int].0@);
                assert(keys.skip(i as int).drop_first() =~= keys.skip(i + 1));
            }
            acc = earlier(obj_due(&self.entries[i].1, now), acc);
        }
        proof {
            assert(keys.skip(0) =~= keys);
        }
        acc
    }
}

pub open spec fn nat_v(o: Option<u64>) -> Option<nat> {
    match o { Some(x) => Some(x as nat), None => None }
}

/// `spec_min_nat`, on `u64`s.
fn min_u64(a: Option<u64>, b: Option<u64>) -> (r: Option<u64>)
    ensures
        nat_v(r) == spec_min_nat(nat_v(a), nat_v(b)),
{
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

/// `spec_earlier`.
fn earlier(a: Option<u64>, b: Option<u64>) -> (r: Option<u64>)
    ensures
        r == spec_earlier(a, b),
{
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

// ---------------------------------------------------------------------------
// Persisted-document validation
// ---------------------------------------------------------------------------

/// Build the origin of an identifier without relying on the host string
/// splitter used by `echod_types::origin_of`.
fn origin_from(text: &str, at: usize) -> (r: String)
    requires
        at <= text@.len(),
    ensures
        r@ == origin(text@.skip(at as int)),
    decreases
        text@.len() - at,
{
    let len = text.unicode_len();
    if at == len || text.get_char(at) == ':' {
        String::new()
    } else {
        let c = text.get_char(at);
        let mut result = String::new();
        result.push(c);
        let rest = origin_from(text, at + 1);
        result.push_str(rest.as_str());
        proof {
            assert(text@.skip(at as int)[0] == c);
            assert(text@.skip(at as int).drop_first()
                == text@.skip(at as int + 1));
        }
        result
    }
}

fn same_origin_verified(a: &String, b: &String) -> (r: bool)
    ensures
        r == (origin(a@) == origin(b@)),
{
    proof {
        assert(a@.skip(0) =~= a@);
        assert(b@.skip(0) =~= b@);
    }
    let ao = origin_from(a.as_str(), 0);
    let bo = origin_from(b.as_str(), 0);
    ao == bo
}

fn origin_is_verified(id: &String, expected: &String) -> (r: bool)
    ensures
        r == (origin(id@) == expected@),
{
    proof {
        assert(id@.skip(0) =~= id@);
    }
    let actual = origin_from(id.as_str(), 0);
    actual == *expected
}

fn unique_strings(values: &Vec<String>) -> (r: bool)
    ensures
        r == crate::document::unique(strs_v(values@)),
{
    let mut i: usize = 0;
    while i < values.len()
        invariant
            i <= values.len(),
            forall|a: int, b: int|
                0 <= a < b < values.len() && a < i ==>
                    strs_v(values@)[a] != strs_v(values@)[b],
        decreases values.len() - i,
    {
        let mut j = i + 1;
        while j < values.len()
            invariant
                i < values.len(),
                i + 1 <= j <= values.len(),
                forall|a: int, b: int|
                    0 <= a < b < values.len() && a < i ==>
                        strs_v(values@)[a] != strs_v(values@)[b],
                forall|b: int|
                    i < b < j ==> strs_v(values@)[i as int] != strs_v(values@)[b],
            decreases values.len() - j,
        {
            if values[i] == values[j] {
                assert(strs_v(values@)[i as int] == strs_v(values@)[j as int]);
                assert(!crate::document::unique(strs_v(values@)));
                return false;
            }
            j += 1;
        }
        proof {
            assert forall|a: int, b: int|
                0 <= a < b < values.len() && a < i + 1
            implies strs_v(values@)[a] != strs_v(values@)[b] by {
                if a < i {
                } else {
                    assert(a == i);
                }
            };
        }
        i += 1;
    }
    proof {
        assert forall|a: int, b: int|
            0 <= a < strs_v(values@).len()
                && 0 <= b < strs_v(values@).len()
                && strs_v(values@)[a] == strs_v(values@)[b]
            implies a == b by {
            if a < b {
                assert(strs_v(values@)[a] != strs_v(values@)[b]);
            } else if b < a {
                assert(strs_v(values@)[b] != strs_v(values@)[a]);
            }
        };
    }
    true
}

fn value_is_empty(value: &Value) -> (r: bool)
    ensures
        r == crate::document::value_empty(*value),
{
    value.data.is_none() && value.headers.len() == 0
}

proof fn lemma_prom_string_views(promise: &Prom)
    ensures
        promise@.callbacks == strs_v(promise.callbacks@),
        promise@.listeners == strs_v(promise.listeners@),
{
}

proof fn lemma_obj_promise_view(object: &Obj)
    ensures
        object@.promise == object.promise@,
{
}

fn validate_promise(
    id: &String,
    object: &Obj,
    committed_at: u64,
) -> (r: bool)
    ensures
        r == crate::document::promise_well_formed(id@, object@, committed_at),
{
    if object.promise.timeout_at > MAX_TIME
        || object.promise.created_at > object.promise.timeout_at
        || object.promise.created_at > committed_at
        || ((object.promise.state == PromiseState::Pending)
            != object.promise.settled_at.is_none())
    {
        return false;
    }
    match object.promise.settled_at {
        Some(at) if at < object.promise.created_at
            || at > object.promise.timeout_at
            || at > committed_at =>
            return false,
        _ => {},
    }
    if object.promise.state == PromiseState::Pending
        && (object.promise.timeout_at <= committed_at
            || !value_is_empty(&object.promise.value))
    {
        return false;
    }
    if object.promise.state == PromiseState::RejectedTimedout
        && object.promise.settled_at != Some(object.promise.timeout_at)
    {
        return false;
    }
    if object.promise.settled_at == Some(object.promise.timeout_at)
        && !value_is_empty(&object.promise.value)
    {
        return false;
    }
    if !unique_strings(&object.promise.callbacks)
        || !unique_strings(&object.promise.listeners)
        || contains_str(&object.promise.callbacks, id)
    {
        return false;
    }
    let mut i: usize = 0;
    while i < object.promise.callbacks.len()
        invariant
            i <= object.promise.callbacks.len(),
            forall|j: int| 0 <= j < i ==>
                origin(strs_v(object.promise.callbacks@)[j]) == origin(id@),
        decreases object.promise.callbacks.len() - i,
    {
        if !same_origin_verified(&object.promise.callbacks[i], id) {
            proof {
                assert(strs_v(object.promise.callbacks@)[i as int]
                    == object.promise.callbacks@[i as int]@);
                assert(origin(strs_v(object.promise.callbacks@)[i as int])
                    != origin(id@));
                assert(!(forall|j: int|
                    0 <= j < object.promise.callbacks@.len() ==>
                        origin(strs_v(object.promise.callbacks@)[j])
                            == origin(id@)));
                lemma_prom_string_views(&object.promise);
                lemma_obj_promise_view(object);
                assert(object@.promise.callbacks
                    == strs_v(object.promise.callbacks@));
                assert(!(forall|j: int|
                    0 <= j < object@.promise.callbacks.len() ==>
                        origin(object@.promise.callbacks[j])
                            == origin(id@)));
                assert(!crate::document::promise_well_formed(
                    id@, object@, committed_at));
            }
            return false;
        }
        i += 1;
    }
    if (object.promise.callbacks.len() > 0
            || object.promise.listeners.len() > 0)
        && !awaitable(&object.promise.tags)
    {
        return false;
    }
    if object.promise.state != PromiseState::Pending
        && (object.promise.callbacks.len() != 0
            || object.promise.listeners.len() != 0)
    {
        return false;
    }
    true
}

fn validate_task(object: &Obj, committed_at: u64) -> (r: bool)
    ensures
        r == crate::document::task_well_formed(object@, committed_at),
{
    if object.task.is_some() != targeted(&object.promise.tags) {
        return false;
    }
    match &object.task {
        None => true,
        Some(task) => {
            let acquired = task.state == TaskState::Acquired;
            let pending = task.state == TaskState::Pending;
            if acquired != task.pid.is_some()
                || acquired != task.ttl.is_some()
                || acquired != task.lease_timeout_at.is_some()
                || pending != task.retry_timeout_at.is_some()
            {
                return false;
            }
            match task.ttl {
                Some(ttl) if ttl == 0 || ttl > MAX_TIME => return false,
                _ => {},
            }
            if acquired
                && (task.version == 0
                    || task.lease_timeout_at.unwrap() <= committed_at)
            {
                return false;
            }
            if pending && task.retry_timeout_at.unwrap() <= committed_at {
                return false;
            }
            let cleared = task.pid.is_none()
                && task.ttl.is_none()
                && task.lease_timeout_at.is_none()
                && task.retry_timeout_at.is_none();
            if task.state == TaskState::Fulfilled
                && (!cleared
                    || task.resumes.len() != 0
                    || object.promise.state == PromiseState::Pending)
            {
                return false;
            }
            if task.state == TaskState::Suspended
                && (!cleared || task.resumes.len() != 0)
            {
                return false;
            }
            if task.state == TaskState::Halted && !cleared {
                return false;
            }
            if object.promise.state != PromiseState::Pending
                && task.state != TaskState::Fulfilled
            {
                return false;
            }
            unique_strings(&task.resumes) && task.version <= MAX_VERSION
        },
    }
}

fn validate_callback_target(
    objects: &Objects,
    callback: &String,
) -> (r: bool)
    ensures
        r == (
            objects@.contains_key(callback@)
                && objects@[callback@].task is Some
                && spec_targeted(objects@[callback@].promise.tags)
        ),
{
    proof {
        use_type_invariant(objects);
    }
    let mut i: usize = 0;
    while i < objects.entries.len()
        invariant
            i <= objects.entries.len(),
            spec_sorted_entries(objects.entries@),
            forall|j: int| 0 <= j < i ==>
                objects.entries@[j].0@ != callback@,
        decreases objects.entries.len() - i,
    {
        if objects.entries[i].0 == *callback {
            proof {
                lemma_sorted_index(objects.entries@, i as int);
            }
            let target = &objects.entries[i].1;
            return target.task.is_some() && targeted(&target.promise.tags);
        }
        i += 1;
    }
    proof {
        lemma_key_set(objects.entries@, callback@);
        assert(!spec_has_key(objects.entries@, callback@));
    }
    false
}

fn validate_callback_targets(objects: &Objects, object: &Obj) -> (r: bool)
    ensures
        r == crate::document::callback_targets_well_formed(objects@, object@),
{
    let mut i: usize = 0;
    while i < object.promise.callbacks.len()
        invariant
            i <= object.promise.callbacks.len(),
            forall|j: int| 0 <= j < i ==> {
                let callback = #[trigger] strs_v(object.promise.callbacks@)[j];
                &&& objects@.contains_key(callback)
                &&& objects@[callback].task is Some
                &&& spec_targeted(objects@[callback].promise.tags)
            },
        decreases object.promise.callbacks.len() - i,
    {
        if !validate_callback_target(objects, &object.promise.callbacks[i]) {
            proof {
                let callback = strs_v(object.promise.callbacks@)[i as int];
                assert(callback == object.promise.callbacks@[i as int]@);
                assert(!(objects@.contains_key(callback)
                    && objects@[callback].task is Some
                    && spec_targeted(objects@[callback].promise.tags)));
                assert(!crate::document::callback_targets_well_formed(
                    objects@, object@));
            }
            return false;
        }
        i += 1;
    }
    true
}

fn has_reverse_callback(objects: &Objects, id: &String) -> (r: bool)
    ensures
        r == exists|awaited: Seq<char>|
            objects@.contains_key(awaited)
                && objects@[awaited].promise.callbacks.contains(id@),
{
    proof {
        use_type_invariant(objects);
    }
    let mut i: usize = 0;
    while i < objects.entries.len()
        invariant
            i <= objects.entries.len(),
            spec_sorted_entries(objects.entries@),
            forall|j: int| 0 <= j < i ==>
                !objects.entries@[j].1@.promise.callbacks.contains(id@),
        decreases objects.entries.len() - i,
    {
        if contains_str(&objects.entries[i].1.promise.callbacks, id) {
            proof {
                lemma_sorted_index(objects.entries@, i as int);
            }
            return true;
        }
        i += 1;
    }
    proof {
        assert forall|awaited: Seq<char>| objects@.contains_key(awaited) implies
            !objects@[awaited].promise.callbacks.contains(id@) by {
            lemma_objs_key(objects.entries@, awaited);
            let j = spec_index(objects.entries@, awaited);
            assert(0 <= j < objects.entries@.len());
            assert(objects.entries@[j].0@ == awaited);
            assert(objects@[awaited] == objects.entries@[j].1@);
        };
    }
    false
}

fn validate_suspended_rung(
    objects: &Objects,
    id: &String,
    object: &Obj,
) -> (r: bool)
    ensures
        r == crate::document::suspended_rung_well_formed(objects@, id@, object@),
{
    match &object.task {
        Some(task) if task.state == TaskState::Suspended
            && object.promise.state == PromiseState::Pending =>
                has_reverse_callback(objects, id),
        _ => true,
    }
}

fn validate_workflow_ids_bounded(workflow: &WorkflowDocument) -> (r: bool)
    ensures
        r,
        crate::document::document_ids_bounded(
            StoredDocumentV::Workflow(workflow@),
        ),
{
    proof {
        use_type_invariant(&workflow.objects);
    }
    let mut i: usize = 0;
    while i < workflow.objects.entries.len()
        invariant
            i <= workflow.objects.entries.len(),
            spec_sorted_entries(workflow.objects.entries@),
            forall|j: int| 0 <= j < i ==>
                workflow.objects.entries@[j].0@.len()
                    <= usize::MAX as int,
        decreases workflow.objects.entries.len() - i,
    {
        let len = workflow.objects.entries[i].0.unicode_len();
        assert(len as nat
            == workflow.objects.entries@[i as int].0@.len());
        i += 1;
    }
    proof {
        assert forall|id: Seq<char>|
            workflow.objects@.contains_key(id) implies
                id.len() <= usize::MAX as int by {
            lemma_objs_key(workflow.objects.entries@, id);
            let j = spec_index(workflow.objects.entries@, id);
            assert(0 <= j < workflow.objects.entries@.len());
            assert(workflow.objects.entries@[j].0@ == id);
        };
    }
    true
}

pub fn validate_workflow_well_formed(workflow: &WorkflowDocument) -> (r: bool)
    ensures
        r == crate::document::workflow_well_formed(workflow@),
        crate::document::document_ids_bounded(
            StoredDocumentV::Workflow(workflow@),
        ),
{
    let ids_bounded = validate_workflow_ids_bounded(workflow);
    assert(ids_bounded);
    if workflow.committed_at > MAX_TIME {
        return false;
    }
    proof {
        use_type_invariant(&workflow.objects);
    }
    let mut i: usize = 0;
    while i < workflow.objects.entries.len()
        invariant
            i <= workflow.objects.entries.len(),
            spec_sorted_entries(workflow.objects.entries@),
            crate::document::document_ids_bounded(
                StoredDocumentV::Workflow(workflow@),
            ),
            forall|j: int| 0 <= j < i ==> {
                let entry = #[trigger] workflow.objects.entries@[j];
                let id = entry.0@;
                let object = entry.1@;
                &&& origin(id) == workflow.document@
                &&& crate::document::promise_well_formed(id, object, workflow.committed_at)
                &&& crate::document::task_well_formed(object, workflow.committed_at)
                &&& crate::document::callback_targets_well_formed(workflow.objects@, object)
                &&& crate::document::suspended_rung_well_formed(workflow.objects@, id, object)
            },
        decreases workflow.objects.entries.len() - i,
    {
        let id = &workflow.objects.entries[i].0;
        let object = &workflow.objects.entries[i].1;
        let origin_ok = origin_is_verified(id, &workflow.document);
        let promise_ok = validate_promise(id, object, workflow.committed_at);
        let task_ok = validate_task(object, workflow.committed_at);
        let targets_ok = validate_callback_targets(&workflow.objects, object);
        let rung_ok =
            validate_suspended_rung(&workflow.objects, id, object);
        if !origin_ok || !promise_ok || !task_ok || !targets_ok || !rung_ok
        {
            proof {
                lemma_sorted_index(workflow.objects.entries@, i as int);
                assert(workflow.objects@[
                    workflow.objects.entries@[i as int].0@
                ] == workflow.objects.entries@[i as int].1@);
                assert(!(origin(workflow.objects.entries@[i as int].0@)
                        == workflow.document@
                    && crate::document::promise_well_formed(
                        workflow.objects.entries@[i as int].0@,
                        workflow.objects.entries@[i as int].1@,
                        workflow.committed_at)
                    && crate::document::task_well_formed(
                        workflow.objects.entries@[i as int].1@,
                        workflow.committed_at)
                    && crate::document::callback_targets_well_formed(
                        workflow.objects@,
                        workflow.objects.entries@[i as int].1@)
                    && crate::document::suspended_rung_well_formed(
                        workflow.objects@,
                        workflow.objects.entries@[i as int].0@,
                        workflow.objects.entries@[i as int].1@)));
                assert(!crate::document::workflow_well_formed(workflow@));
            }
            return false;
        }
        proof {
            assert(origin(workflow.objects.entries@[i as int].0@)
                == workflow.document@);
        }
        i += 1;
    }
    proof {
        assert forall|id: Seq<char>| workflow.objects@.contains_key(id) implies {
            &&& origin(id) == workflow.document@
            &&& crate::document::promise_well_formed(
                id, workflow.objects@[id], workflow.committed_at)
            &&& crate::document::task_well_formed(
                workflow.objects@[id], workflow.committed_at)
            &&& crate::document::callback_targets_well_formed(
                workflow.objects@, workflow.objects@[id])
            &&& crate::document::suspended_rung_well_formed(
                workflow.objects@, id, workflow.objects@[id])
        } by {
            lemma_objs_key(workflow.objects.entries@, id);
            let j = spec_index(workflow.objects.entries@, id);
            assert(0 <= j < workflow.objects.entries@.len());
            assert(workflow.objects.entries@[j].0@ == id);
            assert(workflow.objects@[id] == workflow.objects.entries@[j].1@);
        };
    }
    let deadline = workflow.objects.deadline();
    workflow.next_wake_at == deadline
}

pub fn validate_schedule_well_formed(schedule: &ScheduleDocument) -> (r: bool)
    ensures
        r == crate::document::schedule_well_formed(schedule@),
{
    if schedule.committed_at > MAX_TIME {
        return false;
    }
    match &schedule.schedule {
        Some(row) => {
            if row.id != schedule.document
                || row.promise_timeout > MAX_TIME
                || row.created_at > schedule.committed_at
                || row.created_at > row.next_run_at
                || match row.last_run_at {
                    Some(last) => last < row.created_at || last >= row.next_run_at,
                    None => false,
                }
                || (targeted(&row.promise_tags) && timer(&row.promise_tags))
            {
                return false;
            }
            schedule.next_wake_at == Some(row.next_run_at)
        },
        None => schedule.next_wake_at.is_none(),
    }
}

/// Executable validation is exactly the complete persisted-document
/// predicate. In particular, successful validation is a proof certificate,
/// not merely a structural parse check.
pub fn validate_well_formed(document: &StoredDocument) -> (r: bool)
    ensures
        r == crate::document::well_formed(document@),
        crate::document::document_ids_bounded(document@),
{
    match document {
        StoredDocument::Workflow(workflow) =>
            validate_workflow_well_formed(workflow),
        StoredDocument::Schedule(schedule) =>
            validate_schedule_well_formed(schedule),
    }
}

pub fn validate_loaded_well_formed(document: &LoadedDocument) -> (r: bool)
    ensures
        r == crate::document::well_formed(document@.document),
        crate::document::document_ids_bounded(document@.document),
{
    validate_well_formed(&document.document)
}

// ---------------------------------------------------------------------------
// One object
// ---------------------------------------------------------------------------

/// `spec_project_prom`: a pending promise past its timeout reads as settled.
fn project_prom(p: &Prom, now: u64) -> (r: Prom)
    ensures
        r@ == spec_project_prom(p@, now),
{
    let mut q = copy(p);
    if q.state == PromiseState::Pending && now >= q.timeout_at {
        q.state = if timer(&q.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
        q.settled_at = Some(q.timeout_at);
    }
    q
}

/// `spec_fulfill_task`.
fn fulfill_task(t: &Tk) -> (r: Tk)
    ensures
        r@ == spec_fulfill_task(t@),
{
    proof {
        lemma_strs_empty();
    }
    Tk {
        state: TaskState::Fulfilled,
        version: t.version,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Vec::new(),
    }
}

/// `spec_project_obj`.
fn project_obj(obj: &Obj, now: u64) -> (r: Obj)
    ensures
        r@ == spec_project_obj(obj@, now),
{
    let promise = project_prom(&obj.promise, now);
    let task = match &obj.task {
        Some(t) => {
            if !(promise.state == PromiseState::Pending) && !(t.state == TaskState::Fulfilled) {
                Some(fulfill_task(t))
            } else {
                Some(copy(t))
            }
        },
        None => None,
    };
    Obj { promise, task }
}

/// `spec_record`.
fn record(id: &String, p: &Prom) -> (r: PromiseRecord)
    ensures
        r == spec_record(*id, p@),
{
    PromiseRecord {
        id: id.clone(),
        state: p.state,
        param: copy(&p.param),
        value: copy(&p.value),
        tags: copy(&p.tags),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

/// `spec_task_record`.
fn task_record(id: &String, t: &Tk) -> (r: TaskRecord)
    ensures
        r == spec_task_record(*id, t@),
{
    proof {
        if t@.pid is Some {
            crate::interpret::lemma_string_of(t.pid.unwrap());
        }
    }
    TaskRecord {
        id: id.clone(),
        state: t.state,
        version: t.version,
        resumes: t.resumes.len() as u64,
        ttl: t.ttl,
        pid: match &t.pid { Some(s) => Some(s.clone()), None => None },
    }
}

/// `spec_new_obj`: a promise, and a task when the promise is a target.
fn new_obj(timeout_at: u64, now: u64, param: Value, tags: Tags, runnable: bool) -> (r: Obj)
    ensures
        r@ == spec_new_obj(timeout_at, now, param, tags, runnable),
{
    let live = timeout_at > now;
    let is_timer = timer(&tags);
    let empty = Value::empty();
    proof {
        assert(exists|v: Value| v@ == AValue::empty());
        lemma_value_ext(empty, Value::spec_empty());
        lemma_strs_empty();
    }
    let promise = Prom {
        state: if live { PromiseState::Pending } else if is_timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
        param,
        value: empty,
        tags,
        timeout_at,
        created_at: if live { now } else { timeout_at },
        settled_at: if live { None } else { Some(timeout_at) },
        callbacks: Vec::new(),
        listeners: Vec::new(),
    };
    let task = if runnable {
        Some(Tk {
            state: if live { TaskState::Pending } else { TaskState::Fulfilled },
            version: 0,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            // A newly runnable promise is offered by this transition.  The
            // request drain advances this to `now + retry_timeout` before
            // the document is committed.
            retry_timeout_at: if live { Some(now) } else { None },
            resumes: Vec::new(),
        })
    } else {
        None
    };
    Obj { promise, task }
}

/// `spec_acquire`.
fn acquire(t: &Tk, pid: &String, ttl: u64, now: u64) -> (r: Tk)
    ensures
        r@ == spec_acquire(t@, pid@, ttl, now),
{
    proof {
        lemma_strs_empty();
    }
    Tk {
        state: TaskState::Acquired,
        version: sat_add(t.version, 1),
        pid: Some(pid.clone()),
        ttl: Some(ttl),
        lease_timeout_at: Some(sat_add(now, ttl)),
        retry_timeout_at: None,
        resumes: Vec::new(),
    }
}

/// `spec_unlease`.
fn unlease(t: &Tk, state: TaskState, retry: Option<u64>) -> (r: Tk)
    ensures
        r@ == spec_unlease(t@, state, retry),
{
    Tk {
        state,
        version: t.version,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: retry,
        resumes: copy(&t.resumes),
    }
}

/// `spec_promise_due`.
fn promise_due(obj: &Obj, now: u64) -> (r: Option<u64>)
    ensures
        r == spec_promise_due(obj@, now),
{
    let p = &obj.promise;
    if p.state == PromiseState::Pending && p.timeout_at <= now {
        Some(p.timeout_at)
    } else if !(p.state == PromiseState::Pending) && (p.callbacks.len() > 0 || p.listeners.len() > 0) {
        let at = match p.settled_at { Some(t) => t, None => 0 };
        if at <= now { Some(at) } else { None }
    } else {
        None
    }
}

/// `spec_lease_due`.
fn lease_due(obj: &Obj, now: u64) -> (r: Option<u64>)
    ensures
        r == spec_lease_due(obj@, now),
{
    match &obj.task {
        Some(t) => {
            if obj.promise.state == PromiseState::Pending && t.state == TaskState::Acquired {
                match t.lease_timeout_at {
                    Some(at) => if at <= now { Some(at) } else { None },
                    None => None,
                }
            } else {
                None
            }
        },
        None => None,
    }
}

/// `spec_retry_due`.
fn retry_due(obj: &Obj, now: u64) -> (r: Option<u64>)
    ensures
        r == spec_retry_due(obj@, now),
{
    match &obj.task {
        Some(t) => {
            if obj.promise.state == PromiseState::Pending && t.state == TaskState::Pending {
                match t.retry_timeout_at {
                    Some(at) => if at <= now { Some(at) } else { None },
                    None => None,
                }
            } else {
                None
            }
        },
        None => None,
    }
}

/// `spec_obj_due`.
fn obj_due(obj: &Obj, now: u64) -> (r: Option<u64>)
    ensures
        r == spec_obj_due(obj@, now),
{
    earlier(earlier(promise_due(obj, now), lease_due(obj, now)), retry_due(obj, now))
}

/// `spec_obj_deadline`.
fn obj_deadline(obj: &Obj) -> (r: Option<u64>)
    ensures
        nat_v(r) == spec_obj_deadline(obj@),
{
    obj_due(obj, u64::MAX)
}

// ---------------------------------------------------------------------------
// Documents
// ---------------------------------------------------------------------------

/// `spec_empty_body`.
pub fn empty_body(key: &String) -> (r: DocumentBody)
    ensures
        r@ == spec_empty_body(key@),
{
    if is_schedule_key(key) { DocumentBody::Schedule(None) } else { DocumentBody::Workflow(Objects::empty()) }
}

/// `spec_body_is_empty`.
fn is_empty(doc: &DocumentBody) -> (r: bool)
    ensures
        r == spec_body_is_empty(doc@),
{
    match doc {
        DocumentBody::Workflow(objs) => objs.is_empty(),
        DocumentBody::Schedule(slot) => slot.is_none(),
    }
}

/// `spec_workflow_map`: the objects of an workflow document; none for a schedule.
fn open(doc: DocumentBody) -> (r: Objects)
    ensures
        r@ == spec_workflow_map(doc@),
{
    match doc {
        DocumentBody::Workflow(objs) => objs,
        DocumentBody::Schedule(_) => Objects::empty(),
    }
}

/// `spec_workflow_map(doc)[id]`, copied out, without opening the document.
pub fn peek(doc: &DocumentBody, id: &String) -> (r: Option<Obj>)
    ensures
        match r {
            Some(o) => spec_workflow_map(doc@).contains_key(id@) && o@ == spec_workflow_map(doc@)[id@],
            None => !spec_workflow_map(doc@).contains_key(id@),
        },
{
    match doc {
        DocumentBody::Workflow(objs) => objs.get(id),
        DocumentBody::Schedule(_) => None,
    }
}

/// `spec_body_deadline`.
pub fn body_deadline(doc: &DocumentBody) -> (r: Option<u64>)
    ensures
        nat_v(r) == spec_body_deadline(doc@),
{
    match doc {
        DocumentBody::Schedule(Some(schedule)) => Some(schedule.next_run_at),
        DocumentBody::Workflow(objs) => objs.deadline(),
        DocumentBody::Schedule(None) => None,
    }
}

/// `spec_earliest_in`.
fn earliest_in(doc: &DocumentBody, now: u64) -> (r: Option<u64>)
    ensures
        r == spec_earliest_in(doc@, now),
{
    match doc {
        DocumentBody::Schedule(Some(schedule)) => if schedule.next_run_at <= now { Some(schedule.next_run_at) } else { None },
        DocumentBody::Workflow(objs) => objs.earliest(now),
        DocumentBody::Schedule(None) => None,
    }
}

// ---------------------------------------------------------------------------
// Requests
// ---------------------------------------------------------------------------

/// `spec_key`: the document a request is about.
fn key_of(request: &Request) -> (r: Option<String>)
    ensures
        match r {
            Some(key) => spec_key(*request) == Some(key@),
            None => spec_key(*request) is None,
        },
{
    match request {
        Request::PromiseGet(q) => Some(origin_key(&q.id)),
        Request::PromiseCreate(q) => Some(origin_key(&q.id)),
        Request::PromiseSettle(q) => Some(origin_key(&q.id)),
        Request::PromiseRegisterCallback(q) => Some(origin_key(&q.awaited)),
        Request::PromiseRegisterListener(q) => Some(origin_key(&q.awaited)),
        Request::TaskGet(q) => Some(origin_key(&q.id)),
        Request::TaskCreate(q) => Some(origin_key(&q.action.id)),
        Request::TaskAcquire(q) => Some(origin_key(&q.id)),
        Request::TaskFulfill(q) => Some(origin_key(&q.id)),
        Request::TaskRelease(q) => Some(origin_key(&q.id)),
        Request::TaskHalt(q) => Some(origin_key(&q.id)),
        Request::TaskContinue(q) => Some(origin_key(&q.id)),
        Request::TaskFence(q) => Some(origin_key(&q.id)),
        Request::TaskFenceCheck(q) => Some(origin_key(&q.id)),
        Request::TaskSuspend(q) => Some(origin_key(&q.id)),
        Request::TaskHeartbeat(q) => {
            if q.tasks.len() == 0 { None } else { Some(origin_key(&q.tasks[0].id)) }
        },
        Request::ScheduleGet(q) => Some(schedule_key(&q.id)),
        Request::ScheduleDelete(q) => Some(schedule_key(&q.id)),
        Request::ScheduleCreate(q) => Some(schedule_key(&q.id)),
    }
}

/// `spec_promise_res`.
fn promise_res(status: u16, promise: Option<PromiseRecord>) -> (r: Response)
    ensures
        r == spec_promise_res(status, promise),
{
    Response::Promise(PromiseRes { status, promise })
}

/// `spec_pure`: the answer to a request about no document.
fn pure(request: &Request) -> (r: Response)
    ensures
        r == spec_pure(*request),
{
    match request {
        Request::TaskHeartbeat(q) => {
            if q.tasks.len() == 0 { Response::Status(StatusRes { status: 200 }) } else { unavailable(request) }
        },
        _ => unavailable(request),
    }
}

/// `spec_unavailable`: 503, in the shape the request expects.
fn unavailable(request: &Request) -> (r: Response)
    ensures
        r == spec_unavailable(*request),
{
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => promise_res(503, None),
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => Response::Schedule(ScheduleRes { status: 503, schedule: None }),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => Response::Status(StatusRes { status: 503 }),
        Request::TaskGet(_) => Response::TaskGet(TaskGetRes { status: 503, task: None }),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => Response::TaskClaim(TaskClaimRes { status: 503, task: None, promise: None }),
        Request::TaskFulfill(_) => promise_res(503, None),
        Request::TaskFence(_) => Response::TaskFence(TaskFenceRes { status: 503, action: None }),
    }
}


// ---------------------------------------------------------------------------
// Handlers: one request against one document
// ---------------------------------------------------------------------------

fn status_res(status: u16) -> (r: Response)
    ensures
        r == Response::Status(StatusRes { status }),
{
    Response::Status(StatusRes { status })
}

fn claim_res(status: u16, task: Option<TaskRecord>, promise: Option<PromiseRecord>) -> (r: Response)
    ensures
        r == Response::TaskClaim(TaskClaimRes { status, task, promise }),
{
    Response::TaskClaim(TaskClaimRes { status, task, promise })
}

fn fence_res(status: u16, action: Option<TaskFenceInnerRes>) -> (r: Response)
    ensures
        r == Response::TaskFence(TaskFenceRes { status, action }),
{
    Response::TaskFence(TaskFenceRes { status, action })
}

/// A settled promise, and its task fulfilled: the shared tail of `promise_settle` and `task_fulfill`.
fn settle_obj(seen: Obj, state: PromiseState, value: Value, now: u64) -> (r: Obj)
    ensures
        r@ == (ObjV {
            promise: PromV { state, value, settled_at: Some(now), ..seen@.promise },
            task: match seen@.task {
                Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
                other => other,
            },
        }),
{
    let Obj { promise, task } = seen;
    let mut promise = promise;
    promise.state = state;
    promise.value = value;
    promise.settled_at = Some(now);
    let task = match task {
        Some(t) => if !(t.state == TaskState::Fulfilled) { Some(fulfill_task(&t)) } else { Some(t) },
        None => None,
    };
    Obj { promise, task }
}

/// The awaiter joins the awaited promise's callbacks, once.
fn add_callback(obj: Obj, id: &String) -> (r: Obj)
    ensures
        r@ == (ObjV {
            promise: PromV {
                callbacks: if obj@.promise.callbacks.contains(id@) { obj@.promise.callbacks } else { obj@.promise.callbacks.push(id@) },
                ..obj@.promise
            },
            ..obj@
        }),
{
    let Obj { promise, task } = obj;
    let mut promise = promise;
    if !contains_str(&promise.callbacks, id) {
        push_id(&mut promise.callbacks, id);
    }
    Obj { promise, task }
}

/// The address joins the promise's listeners, once.
fn add_listener(obj: Obj, address: &String) -> (r: Obj)
    ensures
        r@ == (ObjV {
            promise: PromV {
                listeners: if obj@.promise.listeners.contains(address@) { obj@.promise.listeners } else { obj@.promise.listeners.push(address@) },
                ..obj@.promise
            },
            ..obj@
        }),
{
    let Obj { promise, task } = obj;
    let mut promise = promise;
    if !contains_str(&promise.listeners, address) {
        push_id(&mut promise.listeners, address);
    }
    Obj { promise, task }
}

fn promise_get(doc: DocumentBody, id: &String, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_promise_get(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (DocumentBody::Workflow(objs), promise_res(404, None)),
        Some(found) => {
            let obj = project_obj(&found, now);
            let res = promise_res(200, Some(record(id, &obj.promise)));
            (DocumentBody::Workflow(objs), res)
        },
    }
}

fn promise_create(doc: DocumentBody, req: &PromiseCreateReq, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_promise_create(doc@, *req, now),
{
    if req.timeout_at > MAX_TIME || (timer(&req.tags) && targeted(&req.tags)) {
        return (doc, promise_res(400, None));
    }
    match peek(&doc, &req.id) {
        Some(found) => {
            let obj = project_obj(&found, now);
            let res = promise_res(200, Some(record(&req.id, &obj.promise)));
            (doc, res)
        },
        None => {
            let runnable = targeted(&req.tags);
            let obj = new_obj(req.timeout_at, now, copy(&req.param), copy(&req.tags), runnable);
            let res = promise_res(200, Some(record(&req.id, &obj.promise)));
            let objs = open(doc).put(&req.id, obj);
            (DocumentBody::Workflow(objs), res)
        },
    }
}

fn promise_settle(doc: DocumentBody, req: &PromiseSettleReq, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_promise_settle(doc@, *req, now),
{
    if !req.state.settable() {
        return (doc, promise_res(400, None));
    }
    let objs = open(doc);
    match objs.get(&req.id) {
        None => (DocumentBody::Workflow(objs), promise_res(404, None)),
        Some(found) => {
            let seen = project_obj(&found, now);
            if !(seen.promise.state == PromiseState::Pending) {
                let res = promise_res(200, Some(record(&req.id, &seen.promise)));
                (DocumentBody::Workflow(objs), res)
            } else {
                let obj = settle_obj(seen, req.state, copy(&req.value), now);
                let res = promise_res(200, Some(record(&req.id, &obj.promise)));
                (DocumentBody::Workflow(objs.put(&req.id, obj)), res)
            }
        },
    }
}

fn register_callback(doc: DocumentBody, awaited: &String, awaiter: &String, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_register_callback(doc@, *awaited, *awaiter, now),
{
    if *awaited == *awaiter || !same_origin(awaited, awaiter) {
        return (doc, promise_res(400, None));
    }
    let objs = open(doc);
    match objs.get(awaited) {
        None => (DocumentBody::Workflow(objs), promise_res(404, None)),
        Some(a) => match objs.get(awaiter) {
            None => (DocumentBody::Workflow(objs), promise_res(422, None)),
            Some(b) => {
                let awaited_obj = project_obj(&a, now);
                let awaiter_obj = project_obj(&b, now);
                let runnable = targeted(&awaiter_obj.promise.tags);
                let can_await = awaitable(&awaited_obj.promise.tags);
                let both_pending = awaited_obj.promise.state == PromiseState::Pending
                    && awaiter_obj.promise.state == PromiseState::Pending;
                if !runnable || !can_await {
                    (DocumentBody::Workflow(objs), promise_res(422, None))
                } else {
                    let res = promise_res(200, Some(record(awaited, &awaited_obj.promise)));
                    if both_pending {
                        let obj = add_callback(awaited_obj, awaiter);
                        (DocumentBody::Workflow(objs.put(awaited, obj)), res)
                    } else {
                        (DocumentBody::Workflow(objs), res)
                    }
                }
            },
        },
    }
}

fn register_listener(doc: DocumentBody, awaited: &String, address: &String, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_register_listener(doc@, *awaited, *address, now),
{
    let objs = open(doc);
    match objs.get(awaited) {
        None => (DocumentBody::Workflow(objs), promise_res(404, None)),
        Some(found) => {
            let obj = project_obj(&found, now);
            if !awaitable(&obj.promise.tags) {
                (DocumentBody::Workflow(objs), promise_res(422, None))
            } else {
                let res = promise_res(200, Some(record(awaited, &obj.promise)));
                if obj.promise.state == PromiseState::Pending {
                    let obj = add_listener(obj, address);
                    (DocumentBody::Workflow(objs.put(awaited, obj)), res)
                } else {
                    (DocumentBody::Workflow(objs), res)
                }
            }
        },
    }
}

fn task_get(doc: DocumentBody, id: &String, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_task_get(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (DocumentBody::Workflow(objs), Response::TaskGet(TaskGetRes { status: 404, task: None })),
        Some(found) => {
            let obj = project_obj(&found, now);
            match &obj.task {
                None => (DocumentBody::Workflow(objs), Response::TaskGet(TaskGetRes { status: 404, task: None })),
                Some(t) => {
                    let res = Response::TaskGet(TaskGetRes { status: 200, task: Some(task_record(id, t)) });
                    (DocumentBody::Workflow(objs), res)
                },
            }
        },
    }
}

fn task_create(doc: DocumentBody, pid: &String, ttl: u64, action: &PromiseCreateReq, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_task_create(doc@, *pid, ttl, *action, now),
{
    if ttl == 0 || ttl > MAX_TIME || action.timeout_at > MAX_TIME
        || !targeted(&action.tags) || timer(&action.tags) {
        return (doc, claim_res(400, None, None));
    }
    let (doc, created) = promise_create(doc, action, now);
    let rejected = match &created {
        Response::Promise(inner) => inner.status == 400,
        _ => false,
    };
    if rejected {
        return (doc, claim_res(400, None, None));
    }
    match peek(&doc, &action.id) {
        None => (doc, claim_res(422, None, None)),
        Some(found) => {
            let Obj { promise, task } = project_obj(&found, now);
            if !targeted(&promise.tags) {
                return (doc, claim_res(422, None, None));
            }
            match task {
                None => (doc, claim_res(409, None, None)),
                Some(t) => {
                    if t.state == TaskState::Fulfilled {
                        let res = claim_res(200, Some(task_record(&action.id, &t)), Some(record(&action.id, &promise)));
                        (doc, res)
                    } else if t.state == TaskState::Pending && t.version >= MAX_VERSION {
                        (doc, claim_res(409, None, None))
                    } else if t.state == TaskState::Pending {
                        let u = acquire(&t, pid, ttl, now);
                        let res = claim_res(200, Some(task_record(&action.id, &u)), Some(record(&action.id, &promise)));
                        let objs = open(doc).put(&action.id, Obj { promise, task: Some(u) });
                        (DocumentBody::Workflow(objs), res)
                    } else {
                        (doc, claim_res(409, None, None))
                    }
                },
            }
        },
    }
}

/// `Held`, executed.
enum Lease {
    Ok(Obj),
    Missing,
    Stale,
}

spec fn lease_v(lease: Lease) -> Held {
    match lease {
        Lease::Ok(obj) => Held::Ok(obj@),
        Lease::Missing => Held::Missing,
        Lease::Stale => Held::Stale,
    }
}

/// `spec_held`: the task `id` at `version`, acquired and live.
fn held(objs: &Objects, id: &String, version: u64, now: u64) -> (r: Lease)
    ensures
        spec_held(objs@, id@, version, now) == (objs@, lease_v(r)),
{
    match objs.get(id) {
        None => Lease::Missing,
        Some(found) => {
            let obj = project_obj(&found, now);
            let live = match &obj.task {
                None => false,
                Some(t) => t.state == TaskState::Acquired && t.version == version && obj.promise.state == PromiseState::Pending,
            };
            match &obj.task {
                None => Lease::Missing,
                Some(_) => if live { Lease::Ok(obj) } else { Lease::Stale },
            }
        },
    }
}

fn task_acquire(doc: DocumentBody, id: &String, version: u64, pid: &String, ttl: u64, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_task_acquire(doc@, *id, version, *pid, ttl, now),
{
    if ttl == 0 || ttl > MAX_TIME {
        return (doc, claim_res(400, None, None));
    }
    let objs = open(doc);
    match objs.get(id) {
        None => (DocumentBody::Workflow(objs), claim_res(404, None, None)),
        Some(found) => {
            let Obj { promise, task } = project_obj(&found, now);
            match task {
                None => (DocumentBody::Workflow(objs), claim_res(404, None, None)),
                Some(t) => {
                    if !(t.state == TaskState::Pending) || t.version != version
                        || !(promise.state == PromiseState::Pending) || t.version >= MAX_VERSION {
                        (DocumentBody::Workflow(objs), claim_res(409, None, None))
                    } else {
                        let u = acquire(&t, pid, ttl, now);
                        let res = claim_res(200, Some(task_record(id, &u)), Some(record(id, &promise)));
                        (DocumentBody::Workflow(objs.put(id, Obj { promise, task: Some(u) })), res)
                    }
                },
            }
        },
    }
}

fn task_release(doc: DocumentBody, id: &String, version: u64, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_task_release(doc@, *id, version, now),
{
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (DocumentBody::Workflow(objs), status_res(404)),
        Lease::Stale => (DocumentBody::Workflow(objs), status_res(409)),
        Lease::Ok(obj) => {
            let Obj { promise, task } = obj;
            let task = match task {
                Some(t) => Some(unlease(&t, TaskState::Pending, Some(now))),
                None => None,
            };
            (DocumentBody::Workflow(objs.put(id, Obj { promise, task })), status_res(200))
        },
    }
}

fn task_fulfill(doc: DocumentBody, id: &String, version: u64, action: &PromiseSettleReq, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_task_fulfill(doc@, *id, version, *action, now),
{
    if !action.state.settable() {
        return (doc, promise_res(400, None));
    }
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (DocumentBody::Workflow(objs), promise_res(404, None)),
        Lease::Stale => (DocumentBody::Workflow(objs), promise_res(409, None)),
        Lease::Ok(obj) => {
            let obj = settle_obj(obj, action.state, copy(&action.value), now);
            let res = promise_res(200, Some(record(id, &obj.promise)));
            (DocumentBody::Workflow(objs.put(id, obj)), res)
        },
    }
}

fn task_halt(doc: DocumentBody, id: &String, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_task_halt(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (DocumentBody::Workflow(objs), status_res(404)),
        Some(found) => {
            let Obj { promise, task } = project_obj(&found, now);
            match task {
                None => (DocumentBody::Workflow(objs), status_res(404)),
                Some(t) => {
                    if t.state == TaskState::Fulfilled {
                        (DocumentBody::Workflow(objs), status_res(409))
                    } else if t.state == TaskState::Halted {
                        (DocumentBody::Workflow(objs), status_res(200))
                    } else {
                        let obj = Obj { promise, task: Some(unlease(&t, TaskState::Halted, None)) };
                        (DocumentBody::Workflow(objs.put(id, obj)), status_res(200))
                    }
                },
            }
        },
    }
}

fn task_continue(doc: DocumentBody, id: &String, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_task_continue(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (DocumentBody::Workflow(objs), status_res(404)),
        Some(found) => {
            let Obj { promise, task } = project_obj(&found, now);
            match task {
                None => (DocumentBody::Workflow(objs), status_res(404)),
                Some(t) => {
                    if !(t.state == TaskState::Halted) || !(promise.state == PromiseState::Pending) {
                        (DocumentBody::Workflow(objs), status_res(409))
                    } else {
                        let mut u = t;
                        u.state = TaskState::Pending;
                        u.retry_timeout_at = Some(now);
                        (DocumentBody::Workflow(objs.put(id, Obj { promise, task: Some(u) })), status_res(200))
                    }
                },
            }
        },
    }
}

/// `spec_one_origin`: every task in the heartbeat is in the first one's origin.
fn one_origin(tasks: &Vec<TaskRef>) -> (r: bool)
    requires
        tasks.len() > 0,
    ensures
        r == spec_one_origin(tasks@, origin(tasks@[0].id@), 0),
{
    let ghost o = origin(tasks@[0].id@);
    let mut i: usize = 0;
    while i < tasks.len()
        invariant
            i <= tasks.len(),
            o == origin(tasks@[0].id@),
            spec_one_origin(tasks@, o, 0) == spec_one_origin(tasks@, o, i as int),
        decreases tasks.len() - i,
    {
        if !same_origin(&tasks[i].id, &tasks[0].id) {
            return false;
        }
        i += 1;
    }
    true
}

/// `spec_extend`: each acquired task the heartbeat names, leased for another ttl.
fn extend(objs: Objects, pid: &String, tasks: &Vec<TaskRef>, now: u64) -> (r: Objects)
    ensures
        r@ == spec_extend(objs@, pid@, tasks@, now, 0),
{
    let ghost start = objs@;
    let mut objs = objs;
    let mut i: usize = 0;
    while i < tasks.len()
        invariant
            i <= tasks.len(),
            spec_extend(start, pid@, tasks@, now, 0) == spec_extend(objs@, pid@, tasks@, now, i as int),
        decreases tasks.len() - i,
    {
        match objs.get(&tasks[i].id) {
            None => {},
            Some(found) => {
                let Obj { promise, task } = project_obj(&found, now);
                match task {
                    Some(t) => {
                        let mine = match &t.pid { Some(p) => *p == *pid, None => false };
                        if t.state == TaskState::Acquired && t.version == tasks[i].version && mine {
                            let ttl = match t.ttl { Some(n) => n, None => 0 };
                            let at = sat_add(now, ttl);
                            let mut u = t;
                            u.lease_timeout_at = Some(at);
                            objs = objs.put(&tasks[i].id, Obj { promise, task: Some(u) });
                        }
                    },
                    None => {},
                }
            },
        }
        i += 1;
    }
    objs
}

fn heartbeat(doc: DocumentBody, pid: &String, tasks: &Vec<TaskRef>, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_heartbeat(doc@, *pid, tasks@, now),
{
    if tasks.len() == 0 {
        return (doc, status_res(200));
    }
    if !one_origin(tasks) {
        return (doc, status_res(400));
    }
    let objs = extend(open(doc), pid, tasks, now);
    (DocumentBody::Workflow(objs), status_res(200))
}

/// `spec_bad_suspend`: an action awaits the task itself, or another origin.
fn bad_suspend(actions: &Vec<PromiseRegisterCallbackReq>, id: &String) -> (r: bool)
    ensures
        r == spec_bad_suspend(actions@, id@, 0),
{
    let mut i: usize = 0;
    while i < actions.len()
        invariant
            i <= actions.len(),
            spec_bad_suspend(actions@, id@, 0) == spec_bad_suspend(actions@, id@, i as int),
        decreases actions.len() - i,
    {
        if actions[i].awaited == *id || !same_origin(&actions[i].awaited, id) {
            return true;
        }
        i += 1;
    }
    false
}

/// `spec_seen`: whether an awaited id appears before `stop`.
fn seen(actions: &Vec<PromiseRegisterCallbackReq>, id: &String, stop: usize) -> (r: bool)
    requires
        stop <= actions.len(),
    ensures
        r == spec_seen(actions@, id@, 0, stop as int),
{
    let mut j: usize = 0;
    while j < stop
        invariant
            j <= stop,
            stop <= actions.len(),
            spec_seen(actions@, id@, 0, stop as int) == spec_seen(actions@, id@, j as int, stop as int),
        decreases stop - j,
    {
        if actions[j].awaited == *id {
            return true;
        }
        j += 1;
    }
    false
}

/// `spec_distinct_awaited`: no awaited id twice.
fn distinct_awaited(actions: &Vec<PromiseRegisterCallbackReq>) -> (r: bool)
    ensures
        r == spec_distinct_awaited(actions@, 0),
{
    let mut i: usize = 0;
    while i < actions.len()
        invariant
            i <= actions.len(),
            spec_distinct_awaited(actions@, 0) == spec_distinct_awaited(actions@, i as int),
        decreases actions.len() - i,
    {
        if seen(actions, &actions[i].awaited, i) {
            return false;
        }
        i += 1;
    }
    true
}

/// `spec_missing_awaited`.
fn missing_awaited(objs: &Objects, actions: &Vec<PromiseRegisterCallbackReq>) -> (r: bool)
    ensures
        r == spec_missing_awaited(objs@, actions@, 0),
{
    let mut i: usize = 0;
    while i < actions.len()
        invariant
            i <= actions.len(),
            spec_missing_awaited(objs@, actions@, 0) == spec_missing_awaited(objs@, actions@, i as int),
        decreases actions.len() - i,
    {
        if !objs.contains(&actions[i].awaited) {
            return true;
        }
        i += 1;
    }
    false
}

/// `spec_unawaitable`.
fn unawaitable(objs: &Objects, actions: &Vec<PromiseRegisterCallbackReq>) -> (r: bool)
    ensures
        r == spec_unawaitable(objs@, actions@, 0),
{
    let mut i: usize = 0;
    while i < actions.len()
        invariant
            i <= actions.len(),
            spec_unawaitable(objs@, actions@, 0) == spec_unawaitable(objs@, actions@, i as int),
        decreases actions.len() - i,
    {
        match objs.get(&actions[i].awaited) {
            Some(obj) => {
                if !awaitable(&obj.promise.tags) {
                    return true;
                }
            },
            None => {},
        }
        i += 1;
    }
    false
}

/// `spec_any_settled`.
fn any_settled(objs: &Objects, actions: &Vec<PromiseRegisterCallbackReq>, now: u64) -> (r: bool)
    ensures
        r == spec_any_settled(objs@, actions@, now, 0),
{
    let mut i: usize = 0;
    while i < actions.len()
        invariant
            i <= actions.len(),
            spec_any_settled(objs@, actions@, now, 0) == spec_any_settled(objs@, actions@, now, i as int),
        decreases actions.len() - i,
    {
        match objs.get(&actions[i].awaited) {
            Some(obj) => {
                let projected = project_obj(&obj, now);
                if !(projected.promise.state == PromiseState::Pending) {
                    return true;
                }
            },
            None => {},
        }
        i += 1;
    }
    false
}

/// `spec_add_callbacks` keeps the keys.
proof fn lemma_add_callbacks_dom(map: Map<Seq<char>, ObjV>, id: Seq<char>, actions: Seq<PromiseRegisterCallbackReq>, i: int)
    ensures
        spec_add_callbacks(map, id, actions, i).dom() == map.dom(),
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() {
    } else if !map.contains_key(actions[i].awaited@) {
        lemma_add_callbacks_dom(map, id, actions, i + 1);
    } else {
        let obj = map[actions[i].awaited@];
        let callbacks = if obj.promise.callbacks.contains(id) { obj.promise.callbacks } else { obj.promise.callbacks.push(id) };
        let obj = ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj };
        let next = map.insert(actions[i].awaited@, obj);
        lemma_add_callbacks_dom(next, id, actions, i + 1);
        assert(next.dom() =~= map.dom());
    }
}

/// `spec_add_callbacks`: the suspended task joins each awaited promise's callbacks.
fn add_callbacks(objs: Objects, id: &String, actions: &Vec<PromiseRegisterCallbackReq>) -> (r: Objects)
    ensures
        r@ == spec_add_callbacks(objs@, id@, actions@, 0),
{
    let ghost start = objs@;
    let mut objs = objs;
    let mut i: usize = 0;
    while i < actions.len()
        invariant
            i <= actions.len(),
            spec_add_callbacks(start, id@, actions@, 0) == spec_add_callbacks(objs@, id@, actions@, i as int),
        decreases actions.len() - i,
    {
        match objs.get(&actions[i].awaited) {
            None => {},
            Some(obj) => {
                objs = objs.put(&actions[i].awaited, add_callback(obj, id));
            },
        }
        i += 1;
    }
    objs
}

fn suspend(doc: DocumentBody, id: &String, version: u64, actions: &Vec<PromiseRegisterCallbackReq>, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_suspend(doc@, *id, version, actions@, now),
{
    if actions.len() == 0 || bad_suspend(actions, id) || !distinct_awaited(actions) {
        return (doc, status_res(400));
    }
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (DocumentBody::Workflow(objs), status_res(404)),
        Lease::Stale => (DocumentBody::Workflow(objs), status_res(409)),
        Lease::Ok(obj) => {
            if missing_awaited(&objs, actions) || unawaitable(&objs, actions) {
                (DocumentBody::Workflow(objs), status_res(422))
            } else if any_settled(&objs, actions, now) {
                let Obj { promise, task } = obj;
                let task = match task {
                    Some(t) => {
                        let mut u = t;
                        u.resumes = Vec::new();
                        proof {
                            lemma_strs_empty();
                        }
                        Some(u)
                    },
                    None => None,
                };
                (DocumentBody::Workflow(objs.put(id, Obj { promise, task })), status_res(300))
            } else {
                proof {
                    lemma_add_callbacks_dom(objs@, id@, actions@, 0);
                }
                let objs = add_callbacks(objs, id, actions);
                match objs.get(id) {
                    Some(found) => {
                        let Obj { promise, task } = found;
                        let task = match task {
                            Some(t) => {
                                let mut u = unlease(&t, TaskState::Suspended, None);
                                u.resumes = Vec::new();
                                proof {
                                    lemma_strs_empty();
                                }
                                Some(u)
                            },
                            None => None,
                        };
                        (DocumentBody::Workflow(objs.put(id, Obj { promise, task })), status_res(200))
                    },
                    None => {
                        proof {
                            assert(false);
                        }
                        (DocumentBody::Workflow(objs), status_res(500))
                    },
                }
            }
        },
    }
}

fn fence(doc: DocumentBody, id: &String, version: u64, action: &TaskFenceAction, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_fence(doc@, *id, version, *action, now),
{
    let crossed = match action {
        TaskFenceAction::Create(c) => c.id == *id || !same_origin(&c.id, id),
        TaskFenceAction::Settle(st) => st.id == *id || !same_origin(&st.id, id),
    };
    if crossed {
        return (doc, fence_res(400, None));
    }
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (DocumentBody::Workflow(objs), fence_res(404, None)),
        Lease::Stale => (DocumentBody::Workflow(objs), fence_res(409, None)),
        Lease::Ok(_) => {
            let doc = DocumentBody::Workflow(objs);
            match action {
                TaskFenceAction::Create(req) => {
                    let (doc, response) = promise_create(doc, req, now);
                    let inner = match response {
                        Response::Promise(p) => p,
                        _ => PromiseRes { status: 500, promise: None },
                    };
                    (doc, fence_res(200, Some(TaskFenceInnerRes::Create(inner))))
                },
                TaskFenceAction::Settle(req) => {
                    let (doc, response) = promise_settle(doc, req, now);
                    let inner = match response {
                        Response::Promise(p) => p,
                        _ => PromiseRes { status: 500, promise: None },
                    };
                    (doc, fence_res(200, Some(TaskFenceInnerRes::Settle(inner))))
                },
            }
        },
    }
}

fn fence_check(doc: DocumentBody, id: &String, version: u64, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_fence_check(doc@, *id, version, now),
{
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (DocumentBody::Workflow(objs), status_res(404)),
        Lease::Stale => (DocumentBody::Workflow(objs), status_res(409)),
        Lease::Ok(_) => (DocumentBody::Workflow(objs), status_res(200)),
    }
}

fn schedule_get(doc: DocumentBody, id: &String) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_schedule_get(doc@, *id),
{
    let found = match &doc {
        DocumentBody::Schedule(Some(schedule)) => {
            if schedule.id == *id {
                proof {
                    axiom_string_ext(schedule.id, *id);
                }
                Some(copy(schedule))
            } else {
                None
            }
        },
        _ => None,
    };
    match found {
        Some(schedule) => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
        None => (doc, Response::Schedule(ScheduleRes { status: 404, schedule: None })),
    }
}

fn schedule_create(doc: DocumentBody, req: &ScheduleCreateReq, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_schedule_create(doc@, *req, now),
{
    if now > MAX_TIME {
        return (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }));
    }
    let next_run_at = next_cron(&req.cron, now);
    if !deadline_bounded(next_run_at, req.promise_timeout)
        || (targeted(&req.promise_tags) && timer(&req.promise_tags))
    {
        return (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }));
    }
    let existing = match &doc {
        DocumentBody::Schedule(Some(schedule)) => Some(copy(schedule)),
        _ => None,
    };
    match existing {
        Some(schedule) => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
        None => {
            let schedule = Schedule {
                id: req.id.clone(),
                cron: req.cron.clone(),
                promise_id: req.promise_id.clone(),
                promise_timeout: req.promise_timeout,
                promise_param: copy(&req.promise_param),
                promise_tags: copy(&req.promise_tags),
                next_run_at,
                last_run_at: None,
                created_at: now,
            };
            let answer = copy(&schedule);
            (DocumentBody::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(answer) }))
        },
    }
}

fn schedule_delete(doc: DocumentBody, id: &String) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_schedule_delete(doc@, *id),
{
    let matched = match &doc {
        DocumentBody::Schedule(Some(schedule)) => {
            if schedule.id == *id {
                proof {
                    axiom_string_ext(schedule.id, *id);
                }
                true
            } else {
                false
            }
        },
        _ => false,
    };
    if matched {
        (DocumentBody::Schedule(None), status_res(200))
    } else {
        (doc, status_res(404))
    }
}

/// `spec_handle`: the same match.
pub fn handle(doc: DocumentBody, request: &Request, now: u64) -> (r: (DocumentBody, Response))
    ensures
        (r.0@, r.1) == spec_handle(doc@, *request, now),
{
    match request {
        Request::PromiseGet(q) => promise_get(doc, &q.id, now),
        Request::PromiseCreate(q) => promise_create(doc, q, now),
        Request::PromiseSettle(q) => promise_settle(doc, q, now),
        Request::PromiseRegisterCallback(q) => register_callback(doc, &q.awaited, &q.awaiter, now),
        Request::PromiseRegisterListener(q) => register_listener(doc, &q.awaited, &q.address, now),
        Request::TaskGet(q) => task_get(doc, &q.id, now),
        Request::TaskCreate(q) => task_create(doc, &q.pid, q.ttl, &q.action, now),
        Request::TaskAcquire(q) => task_acquire(doc, &q.id, q.version, &q.pid, q.ttl, now),
        Request::TaskFulfill(q) => task_fulfill(doc, &q.id, q.version, &q.action, now),
        Request::TaskRelease(q) => task_release(doc, &q.id, q.version, now),
        Request::TaskHalt(q) => task_halt(doc, &q.id, now),
        Request::TaskContinue(q) => task_continue(doc, &q.id, now),
        Request::TaskHeartbeat(q) => heartbeat(doc, &q.pid, &q.tasks, now),
        Request::TaskSuspend(q) => suspend(doc, &q.id, q.version, &q.actions, now),
        Request::TaskFence(q) => fence(doc, &q.id, q.version, &q.action, now),
        Request::TaskFenceCheck(q) => fence_check(doc, &q.id, q.version, now),
        Request::ScheduleGet(q) => schedule_get(doc, &q.id),
        Request::ScheduleCreate(q) => schedule_create(doc, q, now),
        Request::ScheduleDelete(q) => schedule_delete(doc, &q.id),
    }
}

// ---------------------------------------------------------------------------
// Due work: timeouts, leases, retries, callbacks, listeners, schedules
// ---------------------------------------------------------------------------

proof fn lemma_notes_empty()
    ensures
        notes_v(Seq::<Outbound>::empty()) == Seq::<NoteV>::empty(),
{
    assert(notes_v(Seq::<Outbound>::empty()) =~= Seq::<NoteV>::empty());
}

proof fn lemma_notes_one(note: Outbound)
    ensures
        notes_v(seq![note]) == seq![note@],
{
    assert(notes_v(seq![note]) =~= seq![note@]);
}

proof fn lemma_pend_empty()
    ensures
        pend_v(Seq::<Pending>::empty()) == Seq::<PendingV>::empty(),
{
    assert(pend_v(Seq::<Pending>::empty()) =~= Seq::<PendingV>::empty());
}

proof fn lemma_pend_one(pending: Pending)
    ensures
        pend_v(seq![pending]) == seq![pending@],
{
    assert(pend_v(seq![pending]) =~= seq![pending@]);
}

/// Resume one callback target. A suspended task is offered directly at its
/// next retry slot; no later projection pass is needed.
fn resume(
    objs: Objects,
    awaiter: &String,
    awaited: &String,
    since: u64,
    now: u64,
    retry_timeout: u64,
) -> (r: Objects)
    ensures
        r@ == spec_resume(
            objs@, awaiter@, awaited@, since, now, retry_timeout,
        ),
        r@.dom() == objs@.dom(),
{
    match objs.get(awaiter) {
        None => objs,
        Some(found) => {
            let projected = project_obj(&found, now);
            match projected.task {
                None => objs,
                Some(t) => {
                    if t.state == TaskState::Suspended {
                        let mut resumes: Vec<String> = Vec::new();
                        push_id(&mut resumes, awaited);
                        proof {
                            lemma_strs_empty();
                        }
                        let u = Tk {
                            state: TaskState::Pending,
                            version: t.version,
                            pid: None,
                            ttl: None,
                            lease_timeout_at: None,
                            retry_timeout_at: Some(sat_add(now, retry_timeout)),
                            resumes,
                        };
                        let Obj { promise, task: _ } = found;
                        objs.put(awaiter, Obj { promise, task: Some(u) })
                    } else if t.state == TaskState::Fulfilled {
                        objs
                    } else if contains_str(&t.resumes, awaited) {
                        objs
                    } else {
                        let mut u = t;
                        push_id(&mut u.resumes, awaited);
                        let Obj { promise, task: _ } = found;
                        objs.put(awaiter, Obj { promise, task: Some(u) })
                    }
                },
            }
        },
    }
}

/// Advance one due task directly to its next offered slot. Lease expiry and
/// retry are one projection: no intermediate retry-at-`now` state escapes.
fn project_due_object(obj: &Obj, now: u64, retry_timeout: u64) -> (r: Obj)
    ensures
        r@ == spec_project_due_object(obj@, now, retry_timeout),
{
    if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
        project_obj(obj, now)
    } else if obj.promise.state == PromiseState::Pending {
        let mut next = copy(obj);
        match &obj.task {
            Some(t) if t.state == TaskState::Acquired
                && match t.lease_timeout_at { Some(at) => at <= now, None => false } => {
                let mut task = unlease(t, TaskState::Pending, Some(now));
                task.retry_timeout_at = Some(sat_add(now, retry_timeout));
                next.task = Some(task);
                next
            },
            Some(t) if t.state == TaskState::Pending
                && match t.retry_timeout_at { Some(at) => at <= now, None => false } => {
                let mut task = copy(t);
                task.retry_timeout_at = Some(sat_add(now, retry_timeout));
                next.task = Some(task);
                next
            },
            _ => next,
        }
    } else {
        copy(obj)
    }
}

/// Phase 1 projects every object in the stable workflow snapshot.
fn project_workflow(objs: Objects, now: u64, retry_timeout: u64) -> (r: Objects)
    ensures
        r@ == spec_project_workflow(objs@, now, retry_timeout),
{
    let ghost start = objs@;
    let snapshot = objs.clone().into_entries();
    let mut out = objs;
    let mut i: usize = 0;
    while i < snapshot.len()
        invariant
            i <= snapshot@.len(),
            spec_from_entries(snapshot@) == start,
            spec_sorted_entries(snapshot@),
            forall|j: int| 0 <= j < snapshot@.len() ==>
                start.contains_key(#[trigger] snapshot@[j].0@),
            out@.dom() == start.dom(),
            spec_keys_of(snapshot@) == spec_sorted_present(start),
            out@ == spec_project_keys(
                start,
                spec_keys_of(snapshot@),
                i as nat,
                now,
                retry_timeout,
            ),
        decreases snapshot@.len() - i,
    {
        let id = &snapshot[i].0;
        proof {
            assert(start.contains_key(id@));
            assert(out@.contains_key(id@));
        }
        let obj = out.get(id).unwrap();
        let next = project_due_object(&obj, now, retry_timeout);
        let ghost before = out@;
        out = out.put(id, next);
        proof {
            assert(before.contains_key(id@));
            assert(before.insert(id@, out@[id@]).dom() == before.dom());
        }
        i += 1;
    }
    proof {
        assert(spec_keys_of(snapshot@).len() == snapshot@.len());
        reveal(spec_project_workflow);
    }
    out
}

/// Drain every callback on one settled promise in queue order.
fn drain_settled_callbacks(
    mut objs: Objects,
    id: &String,
    now: u64,
    retry_timeout: u64,
) -> (r: Objects)
    ensures
        r@ == spec_drain_settled_callbacks(
            objs@, id@, now, retry_timeout,
        ),
        r@.dom() == objs@.dom(),
{
    let ghost original = objs@;
    let Some(found) = objs.get(id) else {
        return objs;
    };
    if found.promise.state == PromiseState::Pending {
        return objs;
    }
    let callback_count = found.promise.callbacks.len();
    let mut i: usize = 0;
    while i < callback_count
        invariant
            i <= callback_count,
            objs@.dom() == original.dom(),
            objs@.contains_key(id@),
            objs@[id@].promise.callbacks.len() == callback_count - i,
            objs@ == spec_drain_callbacks(
                original, id@, i as nat, now, retry_timeout,
            ),
        decreases callback_count - i,
    {
        let ghost before = objs@;
        let current = objs.get(id).unwrap();
        let Obj { mut promise, task } = current;
        proof {
            lemma_strs_skip(promise.callbacks@);
        }
        let awaiter = promise.callbacks.remove(0);
        let since = match promise.settled_at { Some(t) => t, None => 0 };
        objs = objs.put(id, Obj { promise, task });
        objs = resume(
            objs, &awaiter, id, since, now, retry_timeout,
        );
        proof {
            reveal(spec_drain_callbacks);
            assert(spec_drain_callbacks(
                original, id@, i as nat, now, retry_timeout,
            ) == before);
            assert(spec_drain_callbacks(
                original, id@, (i + 1) as nat, now, retry_timeout,
            ) == objs@);
        }
        i += 1;
    }
    proof {
        reveal(spec_drain_settled_callbacks);
        assert(original.contains_key(id@));
    }
    objs
}

/// Phase 2 drains every settled queue from the same stable key snapshot.
fn drain_workflow(
    objs: Objects,
    now: u64,
    retry_timeout: u64,
) -> (r: Objects)
    ensures
        r@ == spec_drain_workflow(objs@, now, retry_timeout),
{
    let ghost start = objs@;
    let snapshot = objs.clone().into_entries();
    let mut out = objs;
    let mut i: usize = 0;
    while i < snapshot.len()
        invariant
            i <= snapshot@.len(),
            spec_from_entries(snapshot@) == start,
            spec_sorted_entries(snapshot@),
            forall|j: int| 0 <= j < snapshot@.len() ==>
                start.contains_key(#[trigger] snapshot@[j].0@),
            out@.dom() == start.dom(),
            spec_keys_of(snapshot@) == spec_sorted_present(start),
            out@ == spec_drain_callback_keys(
                start,
                spec_keys_of(snapshot@),
                i as nat,
                now,
                retry_timeout,
            ),
        decreases snapshot@.len() - i,
    {
        proof {
            assert(start.contains_key(snapshot@[i as int].0@));
            assert(out@.contains_key(snapshot@[i as int].0@));
        }
        out = drain_settled_callbacks(
            out, &snapshot[i].0, now, retry_timeout,
        );
        i += 1;
    }
    let ghost resumed = out@;
    let mut j: usize = 0;
    while j < snapshot.len()
        invariant
            j <= snapshot@.len(),
            spec_from_entries(snapshot@) == start,
            spec_sorted_entries(snapshot@),
            forall|k: int| 0 <= k < snapshot@.len() ==>
                resumed.contains_key(
                    #[trigger] snapshot@[k].0@,
                ),
            out@.dom() == resumed.dom(),
            spec_keys_of(snapshot@) == spec_sorted_present(start),
            out@ == spec_clear_listener_keys(
                resumed,
                spec_keys_of(snapshot@),
                j as nat,
            ),
        decreases snapshot@.len() - j,
    {
        let id = &snapshot[j].0;
        let current = out.get(id).unwrap();
        if current.promise.state != PromiseState::Pending {
            let Obj { mut promise, task } = current;
            promise.listeners = Vec::new();
            proof {
                lemma_strs_empty();
            }
            out = out.put(id, Obj { promise, task });
        }
        j += 1;
    }
    proof {
        assert(spec_keys_of(snapshot@).len() == snapshot@.len());
        reveal(spec_drain_workflow);
    }
    out
}

/// Fire one due schedule occurrence. Workflow closure is handled only by
/// [`sweep`].
pub fn fire_schedule(doc: DocumentBody, now: u64) -> (r: (DocumentBody, Vec<Pending>))
    ensures
        spec_fire_schedule(doc@, now) == (r.0@, pend_v(r.1@)),
{
    proof {
        lemma_pend_empty();
    }
    match doc {
        DocumentBody::Schedule(Some(schedule))
            if schedule.next_run_at <= now
                && schedule.next_run_at <= MAX_TIME
                && deadline_bounded(
                    schedule.next_run_at,
                    schedule.promise_timeout,
                ) => {
            let at = schedule.next_run_at;
            let promise = expand(&schedule.promise_id, &schedule.id, at);
            let promise_len = promise.unicode_len();
            assert(promise@.len() == promise_len as int);
            let pending = Pending {
                promise,
                at,
                timeout: schedule.promise_timeout,
                param: copy(&schedule.promise_param),
                tags: copy(&schedule.promise_tags),
            };
            proof {
                lemma_pend_one(pending);
            }
            let mut next = schedule;
            next.last_run_at = Some(at);
            next.next_run_at = next_cron(&next.cron, at);
            let mut born = Vec::new();
            born.push(pending);
            (DocumentBody::Schedule(Some(next)), born)
        },
        other => (other, Vec::new()),
    }
}

/// `spec_occurrence`: the promise a schedule occurrence creates, once it is due.
pub fn create_occurrence(doc: DocumentBody, pending: &Pending, now: u64) -> (r: DocumentBody)
    ensures
        r@ == spec_occurrence(doc@, pending@, now),
{
    let objs = open(doc);
    if objs.contains(&pending.promise) || now < pending.at {
        return DocumentBody::Workflow(objs);
    }
    let timeout_at = sat_add(pending.at, pending.timeout);
    let runnable = targeted(&pending.tags) && !timer(&pending.tags);
    let born = new_obj(timeout_at, now, copy(&pending.param), copy(&pending.tags), runnable);
    let Obj { promise, task } = born;
    let mut promise = promise;
    if timeout_at > pending.at {
        promise.created_at = pending.at;
    }
    let task = match task {
        Some(t) => {
            if t.state == TaskState::Pending {
                let mut u = t;
                u.retry_timeout_at = Some(now);
                Some(u)
            } else {
                Some(t)
            }
        },
        None => None,
    };
    DocumentBody::Workflow(objs.put(&pending.promise, Obj { promise, task }))
}

/// Close an occurrence's origin before inserting it, then close the newly
/// inserted object before returning. Effects are derived from the committed
/// endpoints, so callers release them only after the same document CAS.
pub fn occurrence_transition(
    doc: DocumentBody,
    pending: &Pending,
    now: u64,
    retry_timeout: u64,
) -> (r: (DocumentBody, Vec<Outbound>))
    ensures
        (r.0@, notes_v(r.1@))
            == spec_occurrence_transition(
                doc@,
                pending@,
                now,
                retry_timeout,
            ),
{
    proof {
        lemma_notes_empty();
    }
    let original = copy(&doc);
    let (before, _, _) = sweep(doc, now, retry_timeout);
    let created = create_occurrence(before, pending, now);
    let (after, _, _) = sweep(created, now, retry_timeout);
    let notes = committed_notes(&original, &after, now);
    (after, notes)
}

/// One atomic workflow closure. Phase 1 projects every due promise and task;
/// phase 2 drains settled queues and directly offers resumed tasks.
pub fn sweep(from: DocumentBody, now: u64, retry_timeout: u64) -> (r: (DocumentBody, Vec<Pending>, Vec<Outbound>))
    ensures
        (r.0@, pend_v(r.1@), notes_v(r.2@)) == spec_sweep(from@, now, retry_timeout),
{
    proof {
        lemma_pend_empty();
        lemma_notes_empty();
    }
    let original = copy(&from);
    let DocumentBody::Workflow(objs) = from else {
        return (from, Vec::new(), Vec::new());
    };
    let projected = project_workflow(objs, now, retry_timeout);
    let drained = drain_workflow(projected, now, retry_timeout);
    let after = DocumentBody::Workflow(drained);
    let notes = committed_notes(&original, &after, now);
    (after, Vec::new(), notes)
}

/// Whether a document still has work due at `now`.
pub fn due(doc: &DocumentBody, now: u64) -> (r: bool)
    ensures
        r == (spec_earliest_in(doc@, now) is Some),
{
    earliest_in(doc, now).is_some()
}

fn same_key_string(a: &String, b: &String) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    *a == *b
}

fn same_outbound_key(a: &Outbound, b: &Outbound) -> (r: bool)
    ensures
        r == (spec_note_key(a@) == spec_note_key(b@)),
{
    match (a, b) {
        (Outbound::Execute { id: x, .. }, Outbound::Execute { id: y, .. }) =>
            same_key_string(x, y),
        (
            Outbound::Unblock { address: xa, promise: xp },
            Outbound::Unblock { address: ya, promise: yp },
        ) => same_key_string(xa, ya) && same_key_string(&xp.id, &yp.id),
        _ => false,
    }
}

fn contains_outbound_key(notes: &Vec<Outbound>, note: &Outbound) -> (r: bool)
    ensures
        r == exists|i: int| 0 <= i < notes@.len()
            && spec_note_key(notes@[i]@) == spec_note_key(note@),
{
    let mut i: usize = 0;
    while i < notes.len()
        invariant
            i <= notes@.len(),
            forall|j: int| 0 <= j < i ==>
                spec_note_key(notes@[j]@) != spec_note_key(note@),
        decreases notes@.len() - i,
    {
        if same_outbound_key(&notes[i], note) {
            return true;
        }
        i += 1;
    }
    false
}

/// An Execute survives the atomic request only while the task it names is
/// still pending at that version. The handler may consume work discovered by
/// the pre-sweep (for example by acquiring or settling that task), in which
/// case the not-yet-committed Execute must be cancelled. Unblocks describe a
/// listener removed by closure and cannot be consumed by a later handler.
fn outbound_relevant(doc: &DocumentBody, note: &Outbound) -> (r: bool)
    ensures
        r == spec_note_relevant(doc@, note@),
{
    match note {
        Outbound::Execute { id, version } => match peek(doc, id) {
            Some(object) => match object.task {
                Some(task) => task.state == TaskState::Pending && task.version == *version,
                None => false,
            },
            None => false,
        },
        Outbound::Unblock { .. } => true,
    }
}

/// Canonical insertion-order representation of the keyed effect set.
fn keyed_notes(doc: &DocumentBody, notes: Vec<Outbound>) -> (r: Vec<Outbound>)
    ensures
        notes_v(r@) == spec_keyed_notes(doc@, notes_v(notes@), notes@.len() as nat),
{
    let mut out: Vec<Outbound> = Vec::new();
    let mut i: usize = 0;
    while i < notes.len()
        invariant
            i <= notes@.len(),
            notes_v(out@) == spec_keyed_notes(doc@, notes_v(notes@), i as nat),
        decreases notes@.len() - i,
    {
        let relevant = outbound_relevant(doc, &notes[i]);
        let present = contains_outbound_key(&out, &notes[i]);
        proof {
            assert(notes_v(notes@)[i as int] == notes@[i as int]@);
            assert forall|j: int| 0 <= j < out@.len() implies
                notes_v(out@)[j] == out@[j]@ by {};
            if present {
                let j = choose|j: int| 0 <= j < out@.len()
                    && spec_note_key(out@[j]@) == spec_note_key(notes@[i as int]@);
                assert(0 <= j < notes_v(out@).len());
                assert(spec_note_key(notes_v(out@)[j])
                    == spec_note_key(notes_v(notes@)[i as int]));
            } else {
                assert forall|j: int| 0 <= j < notes_v(out@).len() implies
                    spec_note_key(notes_v(out@)[j])
                        != spec_note_key(notes_v(notes@)[i as int]) by {
                    assert(notes_v(out@)[j] == out@[j]@);
                    assert(notes_v(notes@)[i as int] == notes@[i as int]@);
                };
            }
            assert(spec_keyed_notes(doc@, notes_v(notes@), (i + 1) as nat)
                == spec_keyed_insert(
                    doc@,
                    spec_keyed_notes(doc@, notes_v(notes@), i as nat),
                    notes_v(notes@)[i as int],
                ));
        }
        if relevant && !present {
            let ghost before = out@;
            out.push(copy(&notes[i]));
            proof {
                assert(notes_v(before.push(notes@[i as int])) =~=
                    notes_v(before).push(notes@[i as int]@));
                assert(notes_v(out@)
                    == spec_keyed_notes(doc@, notes_v(notes@), (i + 1) as nat));
            }
        } else {
            proof {
                assert(notes_v(out@)
                    == spec_keyed_notes(doc@, notes_v(notes@), (i + 1) as nat));
            }
        }
        i += 1;
    }
    out
}

fn offer_is_committed(
    before: &Objects,
    after: &Objects,
    id: &String,
    committed_at: u64,
) -> (r: bool)
    ensures
        r == crate::document::offer_committed(
            before@,
            after@,
            id@,
            committed_at,
        ),
{
    let Some(new_obj) = after.get(id) else {
        return false;
    };
    let Some(new_task) = &new_obj.task else {
        return false;
    };
    if new_obj.promise.state != PromiseState::Pending
        || new_task.state != TaskState::Pending
    {
        return false;
    }
    let Some(retry_at) = new_task.retry_timeout_at else {
        return false;
    };
    if retry_at <= committed_at {
        return false;
    }
    let Some(old_obj) = before.get(id) else {
        return true;
    };
    if same_obj(&old_obj, &new_obj) {
        return false;
    }
    match &old_obj.task {
        Some(old_task) if old_task.state == TaskState::Pending => {
            match old_task.retry_timeout_at {
                Some(at) => at <= committed_at,
                None => true,
            }
        },
        _ => true,
    }
}

fn listener_is_committed(
    before: &Objects,
    after: &Objects,
    promise: &String,
    address: &String,
) -> (r: bool)
    ensures
        r == crate::document::listener_committed(
            before@,
            after@,
            promise@,
            address@,
        ),
{
    let Some(old_obj) = before.get(promise) else {
        return false;
    };
    if !contains_str(&old_obj.promise.listeners, address) {
        return false;
    }
    let Some(new_obj) = after.get(promise) else {
        return false;
    };
    new_obj.promise.state != PromiseState::Pending
        && !contains_str(&new_obj.promise.listeners, address)
}

proof fn lemma_notes_push(notes: Seq<Outbound>, note: Outbound)
    ensures
        notes_v(notes.push(note)) == notes_v(notes).push(note@),
{
    lemma_outbound_view(&note);
    assert(notes_v(notes.push(note)) =~= notes_v(notes).push(note@));
}

fn committed_notes(
    before: &DocumentBody,
    after: &DocumentBody,
    committed_at: u64,
) -> (r: Vec<Outbound>)
    ensures
        notes_v(r@) == spec_committed_notes(before@, after@, committed_at),
{
    let (DocumentBody::Workflow(old), DocumentBody::Workflow(new)) = (before, after) else {
        proof {
            lemma_notes_empty();
        }
        return Vec::new();
    };
    proof {
        use_type_invariant(old);
        use_type_invariant(new);
        lemma_sorted_keys(old.entries@);
        lemma_sorted_keys(new.entries@);
    }
    let mut notes = Vec::new();
    let mut i = 0;
    while i < new.entries.len()
        invariant
            i <= new.entries.len(),
            spec_sorted_present(new@) == spec_keys_of(new.entries@),
            notes_v(notes@) == spec_execute_notes(
                old@,
                new@,
                committed_at,
                spec_sorted_present(new@),
                i as nat,
            ),
        decreases new.entries.len() - i,
    {
        let id = &new.entries[i].0;
        assert(spec_sorted_present(new@)[i as int] == id@);
        assert(new@.contains_key(id@));
        if offer_is_committed(old, new, id, committed_at) {
            let obj = new.get(id).unwrap();
            let task = obj.task.unwrap();
            let ghost prior = notes@;
            notes.push(Outbound::Execute {
                id: id.clone(),
                version: task.version,
            });
            proof {
                lemma_notes_push(prior, notes@[prior.len() as int]);
            }
        }
        assert(notes_v(notes@) == spec_execute_notes(
            old@,
            new@,
            committed_at,
            spec_sorted_present(new@),
            (i + 1) as nat,
        ));
        i += 1;
    }
    let ghost execute_notes = notes@;
    let mut j = 0;
    while j < old.entries.len()
        invariant
            j <= old.entries.len(),
            spec_sorted_entries(old.entries@),
            spec_sorted_present(old@) == spec_keys_of(old.entries@),
            notes_v(notes@) == notes_v(execute_notes)
                + spec_unblock_notes(
                    old@,
                    new@,
                    spec_sorted_present(old@),
                    j as nat,
                ),
        decreases old.entries.len() - j,
    {
        let promise = &old.entries[j].0;
        assert(spec_sorted_present(old@)[j as int] == promise@);
        assert(old@.contains_key(promise@)) by {
            lemma_objs_key(old.entries@, promise@);
        }
        let old_obj = old.get(promise).unwrap();
        let mut k = 0;
        let ghost before_promise_notes = notes@;
        while k < old_obj.promise.listeners.len()
            invariant
                k <= old_obj.promise.listeners.len(),
                old@.contains_key(promise@),
                old_obj@ == old@[promise@],
                notes_v(notes@) == notes_v(before_promise_notes)
                    + spec_unblock_notes_for(
                        old@,
                        new@,
                        promise@,
                        strs_v(old_obj.promise.listeners@),
                        k as nat,
                    ),
            decreases old_obj.promise.listeners.len() - k,
        {
            let address = &old_obj.promise.listeners[k];
            assert(strs_v(old_obj.promise.listeners@)[k as int] == address@);
            if listener_is_committed(old, new, promise, address) {
                let new_obj = new.get(promise).unwrap();
                let promise_record = record(promise, &new_obj.promise);
                let ghost prior = notes@;
                let outbound = Outbound::Unblock {
                    address: address.clone(),
                    promise: promise_record,
                };
                let ghost outbound_v = outbound@;
                notes.push(outbound);
                proof {
                    crate::interpret::lemma_string_of(*promise);
                    lemma_notes_push(prior, notes@[prior.len() as int]);
                    assert(outbound_v == NoteV::Unblock {
                        address: address@,
                        promise: spec_record(*promise, new_obj.promise@),
                    });
                    assert(new_obj@ == new@[promise@]);
                }
            }
            assert(notes_v(notes@) == notes_v(before_promise_notes)
                + spec_unblock_notes_for(
                    old@,
                    new@,
                    promise@,
                    strs_v(old_obj.promise.listeners@),
                    (k + 1) as nat,
                ));
            k += 1;
        }
        assert(notes_v(notes@) == notes_v(execute_notes)
            + spec_unblock_notes(
                old@,
                new@,
                spec_sorted_present(old@),
                (j + 1) as nat,
            ));
        j += 1;
    }
    notes
}

/// One complete request transition.
///
/// Workflow work already due is drained before the raw handler, so reads
/// and errors persist the projection they observed.  Work made immediately
/// due by the handler is drained afterwards.  This includes the first
/// Execute (and rearm) for runnable creates, releases, continues, and
/// suspended resumes, and all callbacks/listeners created by settlement.
///
/// The endpoint effects remain conditional on the same document CAS. A lost
/// CAS discards them and recomputes this transition from the reloaded value.
pub fn request_transition(
    doc: DocumentBody,
    request: &Request,
    now: u64,
    retry_timeout: u64,
) -> (r: (DocumentBody, Response, Vec<Pending>, Vec<Outbound>))
    ensures
        (r.0@, r.1, pend_v(r.2@), notes_v(r.3@))
            == spec_request_transition(doc@, *request, now, retry_timeout),
{
    let workflow = match &doc {
        DocumentBody::Workflow(_) => true,
        DocumentBody::Schedule(_) => false,
    };
    if !workflow {
        let (doc, response) = handle(doc, request, now);
        return (doc, response, Vec::new(), Vec::new());
    }

    proof {
        lemma_pend_empty();
        lemma_notes_empty();
    }
    let original = copy(&doc);
    let (before, mut born, mut notes) = sweep(doc, now, retry_timeout);
    let (handled, response) = handle(before, request, now);
    let (after, mut more_born, mut more_notes) =
        sweep(handled, now, retry_timeout);
    let ghost born0 = born@;
    let ghost notes0 = notes@;
    let ghost more_born0 = more_born@;
    let ghost more_notes0 = more_notes@;
    born.append(&mut more_born);
    notes.append(&mut more_notes);
    proof {
        lemma_map_values_add(born0, more_born0);
        lemma_notes_add(notes0, more_notes0);
    }
    // The endpoint pair is authoritative.  Canonicalizing here cancels a
    // pre-sweep Execute consumed by the handler and gives one sequence entry
    // per protocol key, independent of intermediate sweep order.
    let notes = committed_notes(&original, &after, now);
    (after, response, born, notes)
}

proof fn lemma_map_values_add(a: Seq<Pending>, b: Seq<Pending>)
    ensures
        pend_v(a + b) == pend_v(a) + pend_v(b),
{
    assert(pend_v(a + b) =~= pend_v(a) + pend_v(b));
}

proof fn lemma_notes_add(a: Seq<Outbound>, b: Seq<Outbound>)
    ensures
        notes_v(a + b) == notes_v(a) + notes_v(b),
{
    assert(notes_v(a + b) =~= notes_v(a) + notes_v(b));
}

} // verus!

// ---------------------------------------------------------------------------
// The codec. Verus reads it through `spec_encode_body` and `spec_read`: what
// `encode` wrote, `decode` reads back, and a body that does not parse is
// the empty document for the key.
// ---------------------------------------------------------------------------

#[cfg(not(verus_keep_ghost))]
fn encode_body(doc: &DocumentBody) -> Vec<u8> {
    serde_json::to_vec(doc).unwrap_or_default()
}

#[cfg(not(verus_keep_ghost))]
fn decode_body(key: &String, body: &Vec<u8>) -> DocumentBody {
    match serde_json::from_slice::<DocumentBody>(body) {
        Ok(DocumentBody::Workflow(objs)) => DocumentBody::Workflow(objs.in_order()),
        Ok(doc) => doc,
        Err(_) => empty_body(key),
    }
}

#[cfg(not(verus_keep_ghost))]
impl Objects {
    /// The entries in key order, each id once: the shape every `Objects` has.
    /// Byte order on UTF-8 is code point order, the order of `spec_before`.
    fn in_order(self) -> Objects {
        let mut entries = self.entries;
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        entries.dedup_by(|a, b| a.0 == b.0);
        Objects { entries }
    }
}

/// Serialization is uninterpreted under Verus; the records carry no serde there.
#[cfg(verus_keep_ghost)]
fn encode_body(_doc: &DocumentBody) -> Vec<u8> {
    Vec::new()
}

#[cfg(verus_keep_ghost)]
fn decode_body(key: &String, _body: &Vec<u8>) -> DocumentBody {
    empty_body(key)
}

verus! {

pub assume_specification [encode_body](doc: &DocumentBody) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode_body(doc@);

pub assume_specification [decode_body](key: &String, body: &Vec<u8>) -> (r: DocumentBody)
    ensures
        r@ == spec_read(key@, body@);

// ---------------------------------------------------------------------------
// The node: what it sends
// ---------------------------------------------------------------------------

/// The key hash. Trusted: `fnv1a` over the UTF-8 bytes computes `spec_fnv`.
#[verifier::external_body]
fn hash_key(key: &String) -> (r: u64)
    ensures
        r == spec_fnv(key@),
{
    fnv1a(key.as_str())
}

/// `spec_reply`.
fn reply(client: &String, id: u64, response: Response) -> (r: (Pid, Message))
    ensures
        r == spec_reply(client@, id, response),
{
    proof {
        crate::interpret::lemma_string_of(*client);
    }
    (Pid::Outside, Message::Output(Output::Response { client: client.clone(), id, response }))
}

fn one(message: (Pid, Message)) -> (r: Vec<(Pid, Message)>)
    ensures
        r@ == seq![message],
{
    let mut v: Vec<(Pid, Message)> = Vec::new();
    v.push(message);
    v
}

/// `spec_notify`.
fn notify(note: &Outbound) -> (r: (Pid, Message))
    ensures
        r == spec_notify(note@),
{
    match note {
        Outbound::Execute { id, version } => {
            proof {
                crate::interpret::lemma_string_of(*id);
            }
            (Pid::Outside, Message::Output(Output::Dispatch(Dispatch::Execute { id: id.clone(), version: *version })))
        },
        Outbound::Unblock { address, promise } => {
            proof {
                crate::interpret::lemma_string_of(*address);
            }
            (Pid::Outside, Message::Output(Output::Dispatch(Dispatch::Unblock { address: address.clone(), promise: copy(promise) })))
        },
    }
}

proof fn lemma_notes_index(notes: Seq<NoteV>)
    ensures
        spec_notes(notes).len() == notes.len(),
        forall|k: int| 0 <= k < notes.len() ==> #[trigger] spec_notes(notes)[k] == spec_notify(notes[k]),
    decreases notes.len(),
{
    if notes.len() > 0 {
        lemma_notes_index(notes.drop_first());
        assert forall|k: int| 0 <= k < notes.len() implies #[trigger] spec_notes(notes)[k] == spec_notify(notes[k]) by {
            if k > 0 {
                assert(spec_notes(notes)[k] == spec_notes(notes.drop_first())[k - 1]);
                assert(notes.drop_first()[k - 1] == notes[k]);
            }
        };
    }
}

spec fn spec_sent(reply: Option<(Seq<char>, u64, Response)>, notes: Seq<NoteV>) -> Seq<(Pid, Message)> {
    (match reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    }) + spec_notes(notes)
}

/// The reply, then each note: `send + spec_notes(notify)`.
fn sent(reply_slot: &Option<(String, u64, Response)>, notes: &Vec<Outbound>) -> (r: Vec<(Pid, Message)>)
    ensures
        r@ == spec_sent(reply_v(*reply_slot), notes_v(notes@)),
{
    let mut out: Vec<(Pid, Message)> = Vec::new();
    match reply_slot {
        Some(slot) => out.push(reply(&slot.0, slot.1, copy(&slot.2))),
        None => {},
    }
    let ghost head = out@;
    let ghost nv = notes_v(notes@);
    proof {
        lemma_notes_index(nv);
    }
    let mut i: usize = 0;
    while i < notes.len()
        invariant
            i <= notes.len(),
            nv == notes_v(notes@),
            out@.len() == head.len() + i,
            forall|k: int| 0 <= k < head.len() ==> out@[k] == head[k],
            forall|k: int| 0 <= k < i ==> out@[head.len() + k] == spec_notify(nv[k]),
        decreases notes.len() - i,
    {
        out.push(notify(&notes[i]));
        i += 1;
    }
    proof {
        assert(out@ =~= head + spec_notes(nv));
    }
    out
}

// ---------------------------------------------------------------------------
// The node: the cache
// ---------------------------------------------------------------------------

/// `spec_cached_from`, `spec_remember` and `spec_forget` pass the entries that lack the key.
proof fn lemma_cache_unroll(docs: Seq<CachedV>, key: Seq<char>, body: Seq<u8>, etag: Option<Seq<char>>, j: int)
    requires
        0 <= j <= docs.len(),
        forall|k: int| 0 <= k < j ==> #[trigger] docs[k].key != key,
    ensures
        spec_cached_from(docs, key, 0) == spec_cached_from(docs, key, j),
        spec_remember(docs, key, body, etag, 0) == spec_remember(docs, key, body, etag, j),
        spec_forget(docs, key, 0) == spec_forget(docs, key, j),
    decreases j,
{
    if j > 0 {
        lemma_cache_unroll(docs, key, body, etag, j - 1);
    }
}

/// The first cache entry with the key.
fn find_cached(cache: &Vec<Cached>, key: &String) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < cache.len() && cache@[i as int].key@ == key@
                && forall|k: int| 0 <= k < i ==> #[trigger] cache@[k].key@ != key@,
            None => forall|k: int| 0 <= k < cache@.len() ==> #[trigger] cache@[k].key@ != key@,
        },
{
    let mut i: usize = 0;
    while i < cache.len()
        invariant
            i <= cache.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] cache@[k].key@ != key@,
        decreases cache.len() - i,
    {
        if cache[i].key == *key {
            return Some(i);
        }
        i += 1;
    }
    None
}

proof fn lemma_docs_index(cache: Seq<Cached>)
    ensures
        docs_v(cache).len() == cache.len(),
        forall|k: int| 0 <= k < cache.len() ==> #[trigger] docs_v(cache)[k] == cache[k]@,
{
}

/// `spec_remember`: the document under its key, in place or at the end.
fn remember_in(cache: &mut Vec<Cached>, key: &String, doc: DocumentBody, etag: Option<Etag>)
    ensures
        docs_v(final(cache)@) == spec_remember(docs_v(old(cache)@), key@, spec_encode_body(doc@), etag_v(etag), 0),
{
    let ghost before = docs_v(cache@);
    proof {
        lemma_docs_index(cache@);
    }
    let entry = Cached { key: key.clone(), doc, etag };
    let ghost ev = entry@;
    match find_cached(cache, key) {
        Some(i) => {
            proof {
                lemma_cache_unroll(before, key@, ev.body, ev.etag, i as int);
            }
            cache.set(i, entry);
            proof {
                lemma_docs_index(cache@);
                assert(docs_v(cache@) =~= before.update(i as int, ev));
            }
        },
        None => {
            proof {
                lemma_cache_unroll(before, key@, ev.body, ev.etag, before.len() as int);
            }
            cache.push(entry);
            proof {
                lemma_docs_index(cache@);
                assert(docs_v(cache@) =~= before.push(ev));
            }
        },
    }
}

/// `spec_forget`: the key leaves the cache.
fn forget_in(cache: &mut Vec<Cached>, key: &String)
    ensures
        docs_v(final(cache)@) == spec_forget(docs_v(old(cache)@), key@, 0),
{
    let ghost before = docs_v(cache@);
    proof {
        lemma_docs_index(cache@);
    }
    match find_cached(cache, key) {
        Some(i) => {
            proof {
                lemma_cache_unroll(before, key@, Seq::empty(), None, i as int);
            }
            cache.remove(i);
            proof {
                lemma_docs_index(cache@);
                assert(docs_v(cache@) =~= before.take(i as int) + before.skip(i + 1));
            }
        },
        None => {
            proof {
                lemma_cache_unroll(before, key@, Seq::empty(), None, before.len() as int);
            }
        },
    }
}

/// `spec_keep`: an empty document that was never written leaves the cache.
fn keep_in(cache: &mut Vec<Cached>, key: &String, doc: DocumentBody, etag: Option<Etag>)
    ensures
        docs_v(final(cache)@) == spec_keep(docs_v(old(cache)@), key@, doc@, etag_v(etag)),
{
    if is_empty(&doc) && etag.is_none() {
        forget_in(cache, key);
    } else {
        remember_in(cache, key, doc, etag);
    }
}

proof fn lemma_pend_add(a: Seq<Pending>, b: Seq<Pending>)
    ensures
        pend_v(a + b) == pend_v(a) + pend_v(b),
{
    assert(pend_v(a + b) =~= pend_v(a) + pend_v(b));
}

proof fn lemma_pend_skip(a: Seq<Pending>)
    requires
        a.len() > 0,
    ensures
        pend_v(a.remove(0)) == pend_v(a).skip(1),
{
    assert(pend_v(a.remove(0)) =~= pend_v(a).skip(1));
}

/// `spec_flight`: a flight just opened.
fn new_flight(op: u64, key: String, etag: Option<Etag>, now: u64, caller: Option<(String, u64)>, job: Job) -> (r: Flight)
    ensures
        r@ == spec_flight(op, key@, etag_v(etag), now, caller_v(caller), job@),
{
    proof {
        lemma_pend_empty();
        lemma_notes_empty();
    }
    Flight {
        op,
        key,
        writing: false,
        job,
        etag,
        now,
        caller,
        decided: None,
        born: Vec::new(),
        reply: None,
        notify: Vec::new(),
    }
}

/// `(x + 1) as u64`: the counter, wrapping where the model's cast wraps.
fn bump(x: u64) -> (r: u64)
    ensures
        r == (x + 1) as u64,
{
    if x == u64::MAX {
        proof {
            assert((x + 1) as u64 == 0u64) by (bit_vector)
                requires x == u64::MAX;
        }
        0
    } else {
        x + 1
    }
}

spec fn best_v(best: Option<(u64, String)>) -> Option<(u64, Seq<char>)> {
    match best {
        Some((at, key)) => Some((at, key@)),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The node: flights
// ---------------------------------------------------------------------------

impl Node {
    /// `spec_owns`: the keys this node serves.
    fn owns(&self, key: &String) -> (r: bool)
        ensures
            r == spec_owns(self@, key@),
    {
        self.nodes != 0 && hash_key(key) % self.nodes == self.address
    }

    /// `spec_cached`: the document in the cache, and its etag.
    fn cached(&self, key: &String) -> (r: Option<(DocumentBody, Option<Etag>)>)
        ensures
            match r {
                Some((doc, etag)) => spec_cached(self@, key@) == Some(CachedV { key: key@, body: spec_encode_body(doc@), etag: etag_v(etag) }),
                None => spec_cached(self@, key@) is None,
            },
    {
        proof {
            lemma_docs_index(self.cache@);
        }
        match find_cached(&self.cache, key) {
            Some(i) => {
                proof {
                    lemma_cache_unroll(docs_v(self.cache@), key@, Seq::empty(), None, i as int);
                }
                Some((copy(&self.cache[i].doc), copy(&self.cache[i].etag)))
            },
            None => {
                proof {
                    lemma_cache_unroll(docs_v(self.cache@), key@, Seq::empty(), None, self.cache@.len() as int);
                }
                None
            },
        }
    }

    /// `spec_begin`: decide on the cached document, or ask the store for it.
    fn begin(self, key: String, job: Job, now: u64, caller: Option<(String, u64)>) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.next_op < u64::MAX,
        ensures
            (r.0@, r.1@) == spec_begin(self@, key@, job@, now, caller_v(caller)),
    {
        match self.cached(&key) {
            Some((doc, etag)) => {
                proof {
                    axiom_decode_encode_body(doc@);
                }
                let flight = new_flight(0, key, etag, now, caller, job);
                self.decide(flight, doc)
            },
            None => {
                let op = self.next_op;
                let flight = new_flight(op, key.clone(), None, now, caller, job);
                let mut next = self;
                next.flight = Some(flight);
                next.next_op = op + 1;
                proof {
                    crate::interpret::lemma_string_of(key);
                }
                (next, one((Pid::Store, Message::StoreReq { op, request: StoreReq::Get { key } })))
            },
        }
    }

    /// `spec_decide`: run the job; answer at once when the document stands, else write it back.
    fn decide(self, flight: Flight, doc: DocumentBody) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.next_op < u64::MAX,
        ensures
            (r.0@, r.1@) == spec_decide(self@, flight@, doc@),
    {
        proof {
            lemma_pend_empty();
            lemma_notes_empty();
        }
        let Flight { key, job, etag, now, caller, .. } = flight;
        let (next, answer, born, notify): (DocumentBody, Option<Response>, Vec<Pending>, Vec<Outbound>) = match &job {
            Job::External { request } => {
                let (next, response, born, notify) =
                    request_transition(
                        doc,
                        request,
                        now,
                        self.retry_timeout,
                    );
                (next, Some(response), born, notify)
            },
            Job::Due => {
                match doc {
                    DocumentBody::Schedule(_) => {
                        let (next, born) = fire_schedule(doc, now);
                        (next, None, born, Vec::new())
                    },
                    DocumentBody::Workflow(_) => {
                        let (next, born, notify) = sweep(doc, now, self.retry_timeout);
                        (next, None, born, notify)
                    },
                }
            },
            Job::Occurrence(pending) => (create_occurrence(doc, pending, now), None, Vec::new(), Vec::new()),
        };
        let reply_slot: Option<(String, u64, Response)> = match answer {
            Some(response) => match &caller {
                Some(c) => Some((c.0.clone(), c.1, response)),
                None => None,
            },
            None => None,
        };
        let previous: DocumentBody = match self.cached(&key) {
            Some((d, _)) => {
                proof {
                    axiom_decode_encode_body(d@);
                }
                d
            },
            None => empty_body(&key),
        };
        if same_body(&next, &previous) && born.len() == 0 {
            let mut node = self;
            node.flight = None;
            keep_in(&mut node.cache, &key, next, etag);
            let send = sent(&reply_slot, &notify);
            (node, send)
        } else {
            let op = self.next_op;
            let body = encode_body(&next);
            proof {
                crate::simulation::lemma_bytes_of(body);
                axiom_vec_ext(body, spec_bytes(spec_encode_body(next@)));
                crate::interpret::lemma_string_of(key);
            }
            let request = match &etag {
                Some(tag) => {
                    proof {
                        crate::interpret::lemma_string_of(tag.0);
                    }
                    StoreReq::PutIfMatch { key: key.clone(), body, etag: copy(tag) }
                },
                None => StoreReq::PutIfNoneMatch { key: key.clone(), body },
            };
            let flight = Flight {
                op,
                key,
                writing: true,
                job,
                etag,
                now,
                caller,
                decided: Some(next),
                born,
                reply: reply_slot,
                notify,
            };
            let mut node = self;
            node.flight = Some(flight);
            node.next_op = op + 1;
            (node, one((Pid::Store, Message::StoreReq { op, request })))
        }
    }

    /// `spec_commit`: the write landed; the cache, the pending list and the outside learn of it.
    fn commit(self, flight: Flight, tag: Etag) -> (r: (Node, Vec<(Pid, Message)>))
        ensures
            (r.0@, r.1@) == spec_commit(self@, flight@, tag),
    {
        let ghost fv = flight@;
        let Flight { key, decided, born, reply, notify, .. } = flight;
        let mut node = self;
        node.flight = None;
        match decided {
            Some(doc) => remember_in(&mut node.cache, &key, doc, Some(tag)),
            None => {},
        }
        let mut born = born;
        let ghost queued = node.pending@;
        let ghost arriving = born@;
        node.pending.append(&mut born);
        proof {
            lemma_pend_add(queued, arriving);
        }
        let send = sent(&reply, &notify);
        (node, send)
    }

    /// `spec_fail`: the store did not answer; a request is told so.
    fn fail(self, flight: Flight) -> (r: (Node, Vec<(Pid, Message)>))
        ensures
            (r.0@, r.1@) == spec_fail(self@, flight@),
    {
        match &flight.job {
            Job::External { request } => match &flight.caller {
                Some(c) => {
                    let message = reply(&c.0, c.1, unavailable(request));
                    (self, one(message))
                },
                None => (self, Vec::new()),
            },
            _ => (self, Vec::new()),
        }
    }

    /// `spec_store_reply`: the open flight continues with what the store answered.
    fn store_reply(self, op: u64, response: &StoreRes) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.next_op < u64::MAX,
        ensures
            (r.0@, r.1@) == spec_store_reply(self@, op, *response),
    {
        match &self.flight {
            None => (self, Vec::new()),
            Some(f) => {
                let flight = copy(f);
                if flight.op != op {
                    return (self, Vec::new());
                }
                if !flight.writing {
                    match response {
                        StoreRes::Get { result: Ok(got) } => {
                            let (doc, etag): (DocumentBody, Option<Etag>) = match got {
                                Some(pair) => (decode_body(&flight.key, &pair.0), Some(copy(&pair.1))),
                                None => (empty_body(&flight.key), None),
                            };
                            let mut flight = flight;
                            flight.etag = etag;
                            let mut node = self;
                            node.flight = None;
                            node.decide(flight, doc)
                        },
                        StoreRes::Get { result: Err(_) } => {
                            let mut node = self;
                            node.flight = None;
                            node.fail(flight)
                        },
                        _ => (self, Vec::new()),
                    }
                } else {
                    match response {
                        StoreRes::PutIfMatch { result: Ok(tag) }
                        | StoreRes::PutIfNoneMatch { result: Ok(tag) } =>
                            self.commit(flight, copy(tag)),
                        StoreRes::PutIfMatch { result: Err(_) }
                        | StoreRes::PutIfNoneMatch { result: Err(_) } => {
                            let mut node = self;
                            node.flight = None;
                            node.fail(flight)
                        },
                        _ => (self, Vec::new()),
                    }
                }
            },
        }
    }

    /// `spec_request`: a client call opens a flight on its document.
    fn request(self, now: u64, call: &Call) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.next_op < u64::MAX,
        ensures
            (r.0@, r.1@) == spec_request(self@, now, *call),
    {
        match key_of(&call.request) {
            None => {
                let message = reply(&call.client, call.id, pure(&call.request));
                (self, one(message))
            },
            Some(key) => {
                proof {
                    axiom_string_ext(key, key);
                    assert(key@.len() <= usize::MAX as int);
                }
                if !self.owns(&key) {
                    let message = reply(&call.client, call.id, unavailable(&call.request));
                    (self, one(message))
                } else {
                    let job = Job::External { request: copy(&call.request) };
                    self.begin(key, job, now, Some((call.client.clone(), call.id)))
                }
            },
        }
    }

    /// `spec_timeout`: the oldest occurrence owed, else the earliest due document.
    fn timeout(self, now: u64) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.next_op < u64::MAX,
        ensures
            (r.0@, r.1@) == spec_timeout(self@, now),
    {
        if self.flight.is_some() {
            return (self, Vec::new());
        }
        if self.pending.len() > 0 {
            let mut node = self;
            let ghost queued = node.pending@;
            let pending = node.pending.remove(0);
            proof {
                lemma_pend_skip(queued);
            }
            let key = origin_key(&pending.promise);
            proof {
                axiom_string_ext(key, key);
                assert(key@.len() <= usize::MAX as int);
            }
            if !node.owns(&key) {
                return (node, Vec::new());
            }
            return node.begin(key, Job::Occurrence(pending), now, None);
        }
        match self.earliest_due(now) {
            Some(key) => {
                proof {
                    axiom_string_ext(key, key);
                    assert(key@.len() <= usize::MAX as int);
                }
                self.begin(key, Job::Due, now, None)
            },
            None => (self, Vec::new()),
        }
    }

    /// `spec_earliest_key`: the owned document with the earliest due instant.
    fn earliest_due(&self, now: u64) -> (r: Option<String>)
        ensures
            match r {
                Some(key) => spec_earliest_key(self@, now) == Some(key@),
                None => spec_earliest_key(self@, now) is None,
            },
    {
        let ghost docs = docs_v(self.cache@);
        proof {
            lemma_docs_index(self.cache@);
        }
        let mut best: Option<(u64, String)> = None;
        let mut i: usize = 0;
        while i < self.cache.len()
            invariant
                i <= self.cache.len(),
                docs == docs_v(self.cache@),
                docs.len() == self.cache@.len(),
                forall|k: int| 0 <= k < self.cache@.len() ==> #[trigger] docs[k] == self.cache@[k]@,
                spec_earliest_from(self@, docs, 0, now, None) == spec_earliest_from(self@, docs, i as int, now, best_v(best)),
            decreases self.cache.len() - i,
        {
            proof {
                axiom_decode_encode_body(self.cache@[i as int].doc@);
            }
            let entry = &self.cache[i];
            if self.owns(&entry.key) {
                match earliest_in(&entry.doc, now) {
                    Some(at) => {
                        let better = match &best {
                            None => true,
                            Some(b) => at < b.0,
                        };
                        if better {
                            best = Some((at, entry.key.clone()));
                        }
                    },
                    None => {},
                }
            }
            i += 1;
        }
        match best {
            Some((_, key)) => Some(key),
            None => None,
        }
    }

    /// `spec_wake`: when the next timeout is worth delivering; none while a flight is open.
    fn next_wake(&self) -> (r: Option<u64>)
        ensures
            nat_v(r) == spec_wake(self@),
    {
        if self.flight.is_some() {
            return None;
        }
        let ghost docs = docs_v(self.cache@);
        proof {
            lemma_docs_index(self.cache@);
        }
        let mut acc: Option<u64> = None;
        let mut i: usize = self.cache.len();
        while i > 0
            invariant
                i <= self.cache.len(),
                docs == docs_v(self.cache@),
                docs.len() == self.cache@.len(),
                forall|k: int| 0 <= k < self.cache@.len() ==> #[trigger] docs[k] == self.cache@[k]@,
                nat_v(acc) == spec_deadlines(self@, docs, i as int),
            decreases i,
        {
            i -= 1;
            proof {
                axiom_decode_encode_body(self.cache@[i as int].doc@);
            }
            let entry = &self.cache[i];
            if self.owns(&entry.key) {
                acc = min_u64(body_deadline(&entry.doc), acc);
            }
        }
        let from_pending = if self.pending.len() == 0 { None } else { Some(self.pending[0].at) };
        min_u64(from_pending, acc)
    }

    /// A node of the fleet, before its first event: `spec_initial_node`.
    pub fn new(address: u64, nodes: u64, loops: bool, retry_timeout: u64) -> (r: Node)
        ensures
            r@ == spec_initial_node(Fleet { nodes, loops, appendable: false, retry_timeout }, address),
    {
        let r = Node {
            logic: Logic { clock: 0, loops, stopping: false, stopped: false, last_wake: None },
            wake: None,
            next_request: 1,
            address,
            nodes,
            retry_timeout,
            flight: None,
            cache: Vec::new(),
            pending: Vec::new(),
            next_op: 1,
        };
        proof {
            assert(docs_v(r.cache@) =~= Seq::<CachedV>::empty());
            lemma_pend_empty();
        }
        r
    }

    /// Whether a flight is open.
    pub fn busy(&self) -> (r: bool)
        ensures
            r == (self@.flight is Some),
    {
        self.flight.is_some()
    }

    /// The timeout arm of `spec_node`: the arm runs, then the wake and the clock.
    fn after_timeout(&self, now: u64) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.flight is None,
            self.next_op < u64::MAX,
        ensures
            ({
                let (next, send) = spec_timeout(self@, now);
                r.0@ == (NodeV { logic: LogicV { clock: now as nat, last_wake: None, ..self@.logic }, wake: spec_wake(next), ..next })
                && r.1@ == send
            }),
    {
        let (next, send) = copy(self).timeout(now);
        let mut next = next;
        let w = next.next_wake();
        next.wake = w;
        next.logic = Logic {
            clock: now,
            loops: self.logic.loops,
            stopping: self.logic.stopping,
            stopped: self.logic.stopped,
            last_wake: None,
        };
        (next, send)
    }

    /// The request arm of `spec_node`.
    fn after_request(&self, now: u64, call: &Call) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.flight is None,
            self.next_op < u64::MAX,
        ensures
            ({
                let (next, send) = spec_request(self@, now, *call);
                r.0@ == (NodeV {
                    logic: spec_clock(self@.logic, now),
                    next_request: (self@.next_request + 1) as u64,
                    wake: spec_wake(next),
                    ..next
                })
                && r.1@ == send
            }),
    {
        let (next, send) = copy(self).request(now, call);
        let mut next = next;
        let w = next.next_wake();
        next.wake = w;
        next.logic = Logic {
            clock: now,
            loops: self.logic.loops,
            stopping: self.logic.stopping,
            stopped: self.logic.stopped,
            last_wake: self.logic.last_wake,
        };
        next.next_request = bump(self.next_request);
        (next, send)
    }

    /// The store-reply arm of `spec_node`.
    fn after_store_reply(&self, now: u64, op: u64, response: &StoreRes) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.flight is Some,
            self.next_op < u64::MAX,
        ensures
            ({
                let (next, send) = spec_store_reply(self@, op, *response);
                r.0@ == (NodeV { logic: spec_clock(self@.logic, now), wake: spec_wake(next), ..next })
                && r.1@ == send
            }),
    {
        let (next, send) = copy(self).store_reply(op, response);
        let mut next = next;
        let w = next.next_wake();
        next.wake = w;
        next.logic = Logic {
            clock: now,
            loops: self.logic.loops,
            stopping: self.logic.stopping,
            stopped: self.logic.stopped,
            last_wake: self.logic.last_wake,
        };
        (next, send)
    }

    /// The stop arm of `spec_node`.
    fn after_stop(&self, now: u64) -> (r: Node)
        ensures
            r@ == (NodeV { logic: LogicV { clock: now as nat, loops: false, stopping: true, ..self@.logic }, ..self@ }),
    {
        let mut next = copy(self);
        next.logic = Logic {
            clock: now,
            loops: false,
            stopping: true,
            stopped: self.logic.stopped,
            last_wake: self.logic.last_wake,
        };
        next
    }

    /// One event: `spec_node`. The clock moves, the arm runs, the wake is
    /// recomputed. A spent op counter stutters where the model stutters.
    pub fn step(&self, now: Time, event: &ProcessEvent<Pid, Message>) -> (r: Vec<(Node, Vec<(Pid, Message)>)>)
        ensures
            node_results_v(r@) == spec_node(self@, now, *event),
    {
        proof {
            lemma_results_empty();
        }
        match event {
            ProcessEvent::Timeout => match self.wake {
                Some(at) => {
                    if at <= now && self.flight.is_none() && self.next_op < u64::MAX {
                        let (next, send) = self.after_timeout(now);
                        results_one(next, send)
                    } else if at <= now {
                        results_one(copy(self), Vec::new())
                    } else {
                        Vec::new()
                    }
                },
                None => Vec::new(),
            },
            ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(call) } => {
                if self.flight.is_some() || self.next_op == u64::MAX {
                    results_one(copy(self), Vec::new())
                } else {
                    let (next, send) = self.after_request(now, call);
                    results_one(next, send)
                }
            },
            ProcessEvent::Receive { sender: Pid::Store, message: Message::StoreRes { op, response } } => {
                if self.flight.is_none() || self.next_op == u64::MAX {
                    results_one(copy(self), Vec::new())
                } else {
                    let (next, send) = self.after_store_reply(now, *op, response);
                    results_one(next, send)
                }
            },
            ProcessEvent::Receive { sender: Pid::Outside, message: Message::Stop } => {
                results_one(self.after_stop(now), Vec::new())
            },
            _ => Vec::new(),
        }
    }
}

/// A node's results, as the specification sees them.
pub open spec fn node_results_v(pairs: Seq<(Node, Vec<(Pid, Message)>)>) -> Seq<StepResultV<LocalV, Pid, Message>> {
    pairs.map_values(|pair: (Node, Vec<(Pid, Message)>)| StepResultV { state: LocalV::Node(pair.0@), send: pair.1@ })
}

proof fn lemma_results_empty()
    ensures
        node_results_v(Seq::<(Node, Vec<(Pid, Message)>)>::empty()) == Seq::<StepResultV<LocalV, Pid, Message>>::empty(),
{
    assert(node_results_v(Seq::<(Node, Vec<(Pid, Message)>)>::empty()) =~= Seq::<StepResultV<LocalV, Pid, Message>>::empty());
}

/// `spec_one`: the one result of a step.
fn results_one(node: Node, send: Vec<(Pid, Message)>) -> (r: Vec<(Node, Vec<(Pid, Message)>)>)
    ensures
        node_results_v(r@) == spec_one(LocalV::Node(node@), send@),
{
    let ghost nv = node@;
    let ghost sv = send@;
    let mut r: Vec<(Node, Vec<(Pid, Message)>)> = Vec::new();
    r.push((node, send));
    proof {
        assert(node_results_v(r@) =~= spec_one(LocalV::Node(nv), sv));
    }
    r
}

impl echod_rover::rover::Process<(), Pid, Message> for Node {
    fn on_event(
        &self,
        _config: &(),
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> Vec<(Self, Vec<(Pid, Message)>)> {
        self.step(now, event)
    }
}

} // verus!
verus! {

// ---------------------------------------------------------------------------
// The view types
// ---------------------------------------------------------------------------

/// One occurrence the node still owes.
pub struct PendingV {
    pub promise: Seq<char>,
    pub at: u64,
    pub timeout: u64,
    pub param: Value,
    pub tags: Tags,
}

/// A dispatch the flight will send when its write lands.
pub enum NoteV {
    Execute { id: Seq<char>, version: u64 },
    Unblock { address: Seq<char>, promise: PromiseRecord },
}

/// Idempotency key of an outbound protocol effect.
pub enum NoteKeyV {
    Execute(Seq<char>),
    Unblock(Seq<char>, Seq<char>),
}

pub open spec fn spec_note_key(note: NoteV) -> NoteKeyV {
    match note {
        NoteV::Execute { id, .. } => NoteKeyV::Execute(id),
        NoteV::Unblock { address, promise } => NoteKeyV::Unblock(promise.id@, address),
    }
}

pub open spec fn spec_note_relevant(doc: DocumentBodyV, note: NoteV) -> bool {
    match note {
        NoteV::Execute { id, version } => {
            let objects = spec_workflow_map(doc);
            objects.contains_key(id)
                && match objects[id].task {
                    Some(task) => task.state == TaskState::Pending && task.version == version,
                    None => false,
                }
        },
        NoteV::Unblock { .. } => true,
    }
}

pub open spec fn spec_keyed_insert(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    note: NoteV,
) -> Seq<NoteV> {
    if !spec_note_relevant(doc, note) || exists|i: int| 0 <= i < notes.len()
        && spec_note_key(notes[i]) == spec_note_key(note)
    {
        notes
    } else {
        notes.push(note)
    }
}

pub open spec fn spec_keyed_notes(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        spec_keyed_insert(
            doc,
            spec_keyed_notes(doc, notes, (count - 1) as nat),
            notes[count as int - 1],
        )
    }
}

pub open spec fn spec_execute_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    committed_at: u64,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_execute_notes(before, after, committed_at, keys, (count - 1) as nat);
        let id = keys[count as int - 1];
        if crate::document::offer_committed(before, after, id, committed_at) {
            prior.push(NoteV::Execute {
                id,
                version: after[id].task.unwrap().version,
            })
        } else {
            prior
        }
    }
}

pub open spec fn spec_unblock_notes_for(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    promise: Seq<char>,
    listeners: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_unblock_notes_for(
            before,
            after,
            promise,
            listeners,
            (count - 1) as nat,
        );
        let address = listeners[count as int - 1];
        if crate::document::listener_committed(before, after, promise, address) {
            prior.push(NoteV::Unblock {
                address,
                promise: spec_record(spec_string(promise), after[promise].promise),
            })
        } else {
            prior
        }
    }
}

pub open spec fn spec_unblock_notes(
    before: Map<Seq<char>, ObjV>,
    after: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Seq<NoteV>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let prior = spec_unblock_notes(before, after, keys, (count - 1) as nat);
        let promise = keys[count as int - 1];
        prior + spec_unblock_notes_for(
            before,
            after,
            promise,
            before[promise].promise.listeners,
            before[promise].promise.listeners.len(),
        )
    }
}

/// Canonical imperative representation of the endpoint-derived effect set.
pub open spec fn spec_committed_notes(
    before: DocumentBodyV,
    after: DocumentBodyV,
    committed_at: u64,
) -> Seq<NoteV> {
    match (before, after) {
        (DocumentBodyV::Workflow(old), DocumentBodyV::Workflow(new)) => {
            let new_keys = spec_sorted_present(new);
            let old_keys = spec_sorted_present(old);
            spec_execute_notes(old, new, committed_at, new_keys, new_keys.len())
                + spec_unblock_notes(old, new, old_keys, old_keys.len())
        },
        _ => Seq::empty(),
    }
}

pub proof fn lemma_keyed_notes_from_input(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
    k: int,
)
    requires
        count <= notes.len(),
        0 <= k < spec_keyed_notes(doc, notes, count).len(),
    ensures
        exists|j: int| 0 <= j < count
            && spec_keyed_notes(doc, notes, count)[k] == notes[j],
    decreases count,
{
    if count > 0 {
        let prior = spec_keyed_notes(doc, notes, (count - 1) as nat);
        let note = notes[count as int - 1];
        if !spec_note_relevant(doc, note) || exists|i: int| 0 <= i < prior.len()
            && spec_note_key(prior[i]) == spec_note_key(note)
        {
            lemma_keyed_notes_from_input(doc, notes, (count - 1) as nat, k);
        } else if k < prior.len() {
            lemma_keyed_notes_from_input(doc, notes, (count - 1) as nat, k);
        } else {
            assert(k == prior.len());
        }
    }
}

/// What the open flight is doing.
pub enum JobV {
    External(Request),
    Due,
    Occurrence(PendingV),
}

/// The open flight. A proof reads this instead of the private exec fields.
pub struct FlightV {
    pub op: u64,
    pub key: Seq<char>,
    pub writing: bool,
    pub etag: Option<Seq<char>>,
    pub now: u64,
    pub caller: Option<(Seq<char>, u64)>,
    pub job: JobV,
    pub born: Seq<PendingV>,
    pub reply: Option<(Seq<char>, u64, Response)>,
    pub notify: Seq<NoteV>,
    /// `encode` of the document a write is putting.
    pub decided: Option<Seq<u8>>,
}

/// One cached document: the bytes `encode` would write, and the etag the
/// next conditional write must match. `None` is a document that was loaded
/// as absent and then remembered without a version.
pub struct CachedV {
    pub key: Seq<char>,
    pub body: Seq<u8>,
    pub etag: Option<Seq<char>>,
}

/// A node, as a proof sees it.
pub struct NodeV {
    pub logic: LogicV,
    pub wake: Option<nat>,
    pub next_request: u64,
    pub address: nat,
    pub nodes: nat,
    pub retry_timeout: u64,
    pub flight: Option<FlightV>,
    pub documents: Seq<CachedV>,
    pub pending: Seq<PendingV>,
    pub next_op: u64,
}

// ---------------------------------------------------------------------------
// The node, as a specification. `spec_request`, `spec_timeout`, and
// `spec_store_reply` are the arms of `Node::on_event`; the handlers are the
// step on a document. `spec_decode_body_raw` and `spec_encode_body` are the JSON codec of
// a document, the same kind of trusted boundary as the cron engine.
// ---------------------------------------------------------------------------

/// JSON of a document. `encode` / `decode` in the node are this. A body that
/// does not parse is the empty document for that key, the same fallback as
/// `decode`.
pub uninterp spec fn spec_decode_body_raw(body: Seq<u8>) -> Option<DocumentBodyV>;

pub uninterp spec fn spec_encode_body(doc: DocumentBodyV) -> Seq<u8>;

/// The codec round-trips: what `encode` wrote, `decode` reads back.
pub axiom fn axiom_decode_encode_body(doc: DocumentBodyV)
    ensures
        spec_decode_body_raw(spec_encode_body(doc)) == Some(doc),
        spec_encode_body(doc).len() <= usize::MAX as int,
;

pub open spec fn spec_read(key: Seq<char>, body: Seq<u8>) -> DocumentBodyV {
    match spec_decode_body_raw(body) {
        Some(doc) => doc,
        None => spec_empty_body(key),
    }
}

pub open spec fn spec_empty_value() -> Value {
    Value::spec_empty()
}

pub open spec fn spec_owns(node: NodeV, key: Seq<char>) -> bool {
    node.nodes != 0 && spec_fnv(key) % (node.nodes as u64) == (node.address as u64)
}

pub open spec fn spec_cached(node: NodeV, key: Seq<char>) -> Option<CachedV> {
    spec_cached_from(node.documents, key, 0)
}

pub open spec fn spec_cached_from(docs: Seq<CachedV>, key: Seq<char>, i: int) -> Option<CachedV>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() { None }
    else if docs[i].key == key { Some(docs[i]) }
    else { spec_cached_from(docs, key, i + 1) }
}

pub open spec fn spec_body_is_empty(doc: DocumentBodyV) -> bool {
    match doc {
        DocumentBodyV::Workflow(map) => map.dom().len() == 0,
        DocumentBodyV::Schedule(slot) => slot is None,
    }
}

/// `remember`: an empty document with no etag leaves the cache.
pub open spec fn spec_keep(docs: Seq<CachedV>, key: Seq<char>, doc: DocumentBodyV, etag: Option<Seq<char>>) -> Seq<CachedV> {
    if spec_body_is_empty(doc) && etag is None {
        spec_forget(docs, key, 0)
    } else {
        spec_remember(docs, key, spec_encode_body(doc), etag, 0)
    }
}

pub open spec fn spec_remember(docs: Seq<CachedV>, key: Seq<char>, body: Seq<u8>, etag: Option<Seq<char>>, i: int) -> Seq<CachedV>
    decreases docs.len() - i,
{
    let entry = CachedV { key, body, etag };
    if i >= docs.len() {
        docs.push(entry)
    } else if docs[i].key == key {
        docs.update(i, entry)
    } else {
        spec_remember(docs, key, body, etag, i + 1)
    }
}

pub open spec fn spec_forget(docs: Seq<CachedV>, key: Seq<char>, i: int) -> Seq<CachedV>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() { docs }
    else if docs[i].key == key { docs.take(i) + docs.skip(i + 1) }
    else { spec_forget(docs, key, i + 1) }
}

pub open spec fn spec_request(node: NodeV, now: Time, call: Call) -> (NodeV, Seq<(Pid, Message)>) {
    match spec_key(call.request) {
        None => (node, seq![spec_reply(call.client@, call.id, spec_pure(call.request))]),
        Some(key) => {
            if key.len() > usize::MAX as int || !spec_owns(node, key) {
                (node, seq![spec_reply(call.client@, call.id, spec_unavailable(call.request))])
            } else {
                spec_begin(node, key, JobV::External(call.request), now, Some((call.client@, call.id)))
            }
        },
    }
}

pub open spec fn spec_timeout(node: NodeV, now: Time) -> (NodeV, Seq<(Pid, Message)>) {
    if node.flight is Some {
        (node, Seq::empty())
    } else if node.pending.len() > 0 {
        let pending = node.pending[0];
        let node = NodeV { pending: node.pending.skip(1), ..node };
        let key = spec_origin_key(origin(pending.promise));
        if key.len() > usize::MAX as int || !spec_owns(node, key) {
            (node, Seq::empty())
        } else {
            spec_begin(node, key, JobV::Occurrence(pending), now, None)
        }
    } else {
        match spec_earliest_key(node, now) {
            Some(key) => if key.len() <= usize::MAX as int {
                spec_begin(node, key, JobV::Due, now, None)
            } else {
                (node, Seq::empty())
            },
            None => (node, Seq::empty()),
        }
    }
}

pub open spec fn spec_store_reply(node: NodeV, op: u64, response: StoreRes) -> (NodeV, Seq<(Pid, Message)>) {
    match node.flight {
        None => (node, Seq::empty()),
        Some(flight) => {
            if flight.op != op {
                (node, Seq::empty())
            } else if !flight.writing {
                match response {
                    StoreRes::Get { result: Ok(got) } => {
                        let (doc, etag) = match got {
                            Some((body, tag)) => (spec_read(flight.key, body@), Some(tag.0@)),
                            None => (spec_empty_body(flight.key), None),
                        };
                        let flight = FlightV { etag, ..flight };
                        spec_decide(NodeV { flight: None, ..node }, flight, doc)
                    },
                    StoreRes::Get { result: Err(_) } => spec_fail(NodeV { flight: None, ..node }, flight),
                    _ => (node, Seq::empty()),
                }
            } else {
                match response {
                    StoreRes::PutIfMatch { result: Ok(tag) }
                    | StoreRes::PutIfNoneMatch { result: Ok(tag) } =>
                        spec_commit(node, flight, tag),
                    StoreRes::PutIfMatch { result: Err(_) }
                    | StoreRes::PutIfNoneMatch { result: Err(_) } =>
                        spec_fail(NodeV { flight: None, ..node }, flight),
                    _ => (node, Seq::empty()),
                }
            }
        },
    }
}

pub open spec fn spec_flight(op: u64, key: Seq<char>, etag: Option<Seq<char>>, now: Time, caller: Option<(Seq<char>, u64)>, job: JobV) -> FlightV {
    FlightV {
        op,
        key,
        writing: false,
        etag,
        now,
        caller,
        job,
        born: Seq::empty(),
        reply: None,
        notify: Seq::empty(),
        decided: None,
    }
}

pub open spec fn spec_begin(node: NodeV, key: Seq<char>, job: JobV, now: Time, caller: Option<(Seq<char>, u64)>) -> (NodeV, Seq<(Pid, Message)>) {
    match spec_cached(node, key) {
        Some(cached) => spec_decide(node, spec_flight(0, key, cached.etag, now, caller, job), spec_read(key, cached.body)),
        None => {
            let op = node.next_op;
            let flight = spec_flight(op, key, None, now, caller, job);
            (NodeV { flight: Some(flight), next_op: (op + 1) as u64, ..node }, seq![spec_get(op, key)])
        },
    }
}

pub open spec fn spec_decide(node: NodeV, flight: FlightV, doc: DocumentBodyV) -> (NodeV, Seq<(Pid, Message)>) {
    let (next, reply, born, notify) = match flight.job {
        JobV::External(request) => {
            let (next, response, born, notify) =
                spec_request_transition(
                    doc,
                    request,
                    flight.now,
                    node.retry_timeout,
                );
            (next, Some(response), born, notify)
        },
        JobV::Due => spec_due_transition(doc, flight.now, node.retry_timeout),
        JobV::Occurrence(pending) => (spec_occurrence(doc, pending, flight.now), None, Seq::empty(), Seq::empty()),
    };
    let reply = match (flight.caller, reply) {
        (Some((client, id)), Some(response)) => Some((client, id, response)),
        _ => None,
    };
    let previous = match spec_cached(node, flight.key) {
        Some(cached) => spec_read(flight.key, cached.body),
        None => spec_empty_body(flight.key),
    };
    if next == previous && born.len() == 0 {
        let node = NodeV {
            flight: None,
            documents: spec_keep(node.documents, flight.key, next, flight.etag),
            ..node
        };
        let send = match reply {
            Some((client, id, response)) => seq![spec_reply(client, id, response)],
            None => Seq::empty(),
        };
        (node, send + spec_notes(notify))
    } else {
        let op = node.next_op;
        let body = spec_encode_body(next);
        let request = match flight.etag {
            Some(chars) => StoreReq::PutIfMatch {
                key: spec_string(flight.key),
                body: spec_bytes(body),
                etag: Etag(spec_string(chars)),
            },
            None => StoreReq::PutIfNoneMatch { key: spec_string(flight.key), body: spec_bytes(body) },
        };
        let flight = FlightV {
            op,
            writing: true,
            born,
            reply,
            notify,
            decided: Some(body),
            ..flight
        };
        (NodeV { flight: Some(flight), next_op: (op + 1) as u64, ..node }, seq![(Pid::Store, Message::StoreReq { op, request })])
    }
}

pub open spec fn spec_commit(node: NodeV, flight: FlightV, tag: Etag) -> (NodeV, Seq<(Pid, Message)>) {
    let documents = match flight.decided {
        Some(body) => spec_remember(node.documents, flight.key, body, Some(tag.0@), 0),
        None => node.documents,
    };
    let node = NodeV {
        flight: None,
        documents,
        pending: node.pending + flight.born,
        ..node
    };
    let send = match flight.reply {
        Some((client, id, response)) => seq![spec_reply(client, id, response)],
        None => Seq::empty(),
    };
    (node, send + spec_notes(flight.notify))
}

pub open spec fn spec_fail(node: NodeV, flight: FlightV) -> (NodeV, Seq<(Pid, Message)>) {
    match (flight.job, flight.caller) {
        (JobV::External(request), Some((client, id))) => {
            (node, seq![spec_reply(client, id, spec_unavailable(request))])
        },
        _ => (node, Seq::empty()),
    }
}

pub open spec fn spec_origin_key(origin_chars: Seq<char>) -> Seq<char> {
    seq!['o', '/'] + origin_chars
}

pub open spec fn spec_schedule_key(id: Seq<char>) -> Seq<char> {
    seq!['s', '/'] + id
}

pub open spec fn spec_empty_body(key: Seq<char>) -> DocumentBodyV {
    if spec_starts(key, seq!['s', '/']) { DocumentBodyV::Schedule(None) } else { DocumentBodyV::Workflow(Map::empty()) }
}

pub open spec fn spec_key(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseCreate(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseSettle(q) => Some(spec_origin_key(origin(q.id@))),
        Request::PromiseRegisterCallback(q) => Some(spec_origin_key(origin(q.awaited@))),
        Request::PromiseRegisterListener(q) => Some(spec_origin_key(origin(q.awaited@))),
        Request::TaskGet(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskCreate(q) => Some(spec_origin_key(origin(q.action.id@))),
        Request::TaskAcquire(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFulfill(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskRelease(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskHalt(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskContinue(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFence(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskFenceCheck(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskSuspend(q) => Some(spec_origin_key(origin(q.id@))),
        Request::TaskHeartbeat(q) => {
            if q.tasks@.len() == 0 { None } else { Some(spec_origin_key(origin(q.tasks@[0].id@))) }
        },
        Request::ScheduleGet(q) => Some(spec_schedule_key(q.id@)),
        Request::ScheduleDelete(q) => Some(spec_schedule_key(q.id@)),
        Request::ScheduleCreate(q) => Some(spec_schedule_key(q.id@)),
    }
}

pub open spec fn spec_request_document(request: Request) -> Option<Seq<char>> {
    match request {
        Request::PromiseGet(q) => Some(origin(q.id@)),
        Request::PromiseCreate(q) => Some(origin(q.id@)),
        Request::PromiseSettle(q) => Some(origin(q.id@)),
        Request::PromiseRegisterCallback(q) => Some(origin(q.awaited@)),
        Request::PromiseRegisterListener(q) => Some(origin(q.awaited@)),
        Request::TaskGet(q) => Some(origin(q.id@)),
        Request::TaskCreate(q) => Some(origin(q.action.id@)),
        Request::TaskAcquire(q) => Some(origin(q.id@)),
        Request::TaskFulfill(q) => Some(origin(q.id@)),
        Request::TaskRelease(q) => Some(origin(q.id@)),
        Request::TaskHalt(q) => Some(origin(q.id@)),
        Request::TaskContinue(q) => Some(origin(q.id@)),
        Request::TaskFence(q) => Some(origin(q.id@)),
        Request::TaskFenceCheck(q) => Some(origin(q.id@)),
        Request::TaskSuspend(q) => Some(origin(q.id@)),
        Request::TaskHeartbeat(q) =>
            if q.tasks@.len() == 0 { None } else { Some(origin(q.tasks@[0].id@)) },
        Request::ScheduleGet(q) => Some(q.id@),
        Request::ScheduleCreate(q) => Some(q.id@),
        Request::ScheduleDelete(q) => Some(q.id@),
    }
}

pub open spec fn spec_promise_res(status: u16, promise: Option<PromiseRecord>) -> Response {
    Response::Promise(PromiseRes { status, promise })
}

pub open spec fn spec_pure(request: Request) -> Response {
    match request {
        Request::TaskHeartbeat(q) if q.tasks@.len() == 0 => Response::Status(StatusRes { status: 200 }),
        other => spec_unavailable(other),
    }
}

pub open spec fn spec_unavailable(request: Request) -> Response {
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => spec_promise_res(503, None),
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => Response::Schedule(ScheduleRes { status: 503, schedule: None }),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => Response::Status(StatusRes { status: 503 }),
        Request::TaskGet(_) => Response::TaskGet(TaskGetRes { status: 503, task: None }),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => Response::TaskClaim(TaskClaimRes { status: 503, task: None, promise: None }),
        Request::TaskFulfill(_) => spec_promise_res(503, None),
        Request::TaskFence(_) => Response::TaskFence(TaskFenceRes { status: 503, action: None }),
    }
}

/// One request against one document. The same match as `handle`.
pub open spec fn spec_handle(doc: DocumentBodyV, request: Request, now: Time) -> (DocumentBodyV, Response) {
    match request {
        Request::PromiseGet(q) => spec_promise_get(doc, q.id, now),
        Request::PromiseCreate(q) => spec_promise_create(doc, q, now),
        Request::PromiseSettle(q) => spec_promise_settle(doc, q, now),
        Request::PromiseRegisterCallback(q) => spec_register_callback(doc, q.awaited, q.awaiter, now),
        Request::PromiseRegisterListener(q) => spec_register_listener(doc, q.awaited, q.address, now),
        Request::TaskGet(q) => spec_task_get(doc, q.id, now),
        Request::TaskCreate(q) => spec_task_create(doc, q.pid, q.ttl, q.action, now),
        Request::TaskAcquire(q) => spec_task_acquire(doc, q.id, q.version, q.pid, q.ttl, now),
        Request::TaskFulfill(q) => spec_task_fulfill(doc, q.id, q.version, q.action, now),
        Request::TaskRelease(q) => spec_task_release(doc, q.id, q.version, now),
        Request::TaskHalt(q) => spec_task_halt(doc, q.id, now),
        Request::TaskContinue(q) => spec_task_continue(doc, q.id, now),
        Request::TaskHeartbeat(q) => spec_heartbeat(doc, q.pid, q.tasks@, now),
        Request::TaskSuspend(q) => spec_suspend(doc, q.id, q.version, q.actions@, now),
        Request::TaskFence(q) => spec_fence(doc, q.id, q.version, q.action, now),
        Request::TaskFenceCheck(q) => spec_fence_check(doc, q.id, q.version, now),
        Request::ScheduleGet(q) => spec_schedule_get(doc, q.id),
        Request::ScheduleCreate(q) => spec_schedule_create(doc, q, now),
        Request::ScheduleDelete(q) => spec_schedule_delete(doc, q.id),
    }
}

pub open spec fn spec_workflow_map(doc: DocumentBodyV) -> Map<Seq<char>, ObjV> {
    match doc {
        DocumentBodyV::Workflow(map) => map,
        DocumentBodyV::Schedule(_) => Map::empty(),
    }
}

/// `workflow_mut` replaces a schedule document with an empty origin map before it looks anything up.
pub open spec fn spec_opened(doc: DocumentBodyV) -> DocumentBodyV {
    DocumentBodyV::Workflow(spec_workflow_map(doc))
}

pub open spec fn spec_with_workflow(doc: DocumentBodyV, map: Map<Seq<char>, ObjV>) -> DocumentBodyV {
    match doc {
        DocumentBodyV::Schedule(_) => DocumentBodyV::Workflow(map),
        DocumentBodyV::Workflow(_) => DocumentBodyV::Workflow(map),
    }
}

pub open spec fn spec_project_prom(p: PromV, now: Time) -> PromV {
    if p.state == PromiseState::Pending && now >= p.timeout_at {
        PromV {
            state: if spec_timer(p.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
            settled_at: Some(p.timeout_at),
            ..p
        }
    } else {
        p
    }
}

pub open spec fn spec_fulfill_task(t: TkV) -> TkV {
    TkV {
        state: TaskState::Fulfilled,
        pid: None,
        ttl: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_project_obj(obj: ObjV, now: Time) -> ObjV {
    let promise = spec_project_prom(obj.promise, now);
    let task = match obj.task {
        Some(t) if promise.state != PromiseState::Pending && t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
        other => other,
    };
    ObjV { promise, task }
}

pub open spec fn spec_record(id: String, p: PromV) -> PromiseRecord {
    PromiseRecord {
        id,
        state: p.state,
        param: p.param,
        value: p.value,
        tags: p.tags,
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
    }
}

pub open spec fn spec_task_record(id: String, t: TkV) -> TaskRecord {
    TaskRecord {
        id,
        state: t.state,
        version: t.version,
        resumes: if t.resumes.len() > u64::MAX as nat { u64::MAX } else { t.resumes.len() as u64 },
        ttl: t.ttl,
        pid: match t.pid { Some(s) => Some(spec_string(s)), None => None },
    }
}

pub open spec fn spec_timer(tags: Tags) -> bool {
    spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r'], seq!['t','r','u','e'], 0)
}

pub open spec fn spec_targeted(tags: Tags) -> bool {
    spec_tag_key(tags, seq!['r','e','s','o','n','a','t','e',':','t','a','r','g','e','t'], 0)
}

pub open spec fn spec_awaitable(tags: Tags) -> bool {
    spec_targeted(tags)
        || spec_timer(tags)
        || spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','e','x','t','e','r','n','a','l'], seq!['t','r','u','e'], 0)
        || spec_tag_is(tags, seq!['r','e','s','o','n','a','t','e',':','s','c','o','p','e'], seq!['g','l','o','b','a','l'], 0)
}

pub open spec fn spec_tag_is(tags: Tags, key: Seq<char>, value: Seq<char>, i: int) -> bool
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { false }
    else if tags@[i].0@ == key { tags@[i].1@ == value }
    else { spec_tag_is(tags, key, value, i + 1) }
}

pub open spec fn spec_tag_key(tags: Tags, key: Seq<char>, i: int) -> bool
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { false }
    else if tags@[i].0@ == key { true }
    else { spec_tag_key(tags, key, i + 1) }
}

pub open spec fn spec_offer_at(tags: Tags, now: Time) -> u64 {
    match spec_delay(tags, 0) {
        Some(delay) => if delay > now { delay } else { now },
        None => now,
    }
}

pub open spec fn spec_delay(tags: Tags, i: int) -> Option<u64>
    decreases tags@.len() - i,
{
    if i < 0 || i >= tags@.len() { None }
    else if tags@[i].0@ == seq!['r', 'e', 's', 'o', 'n', 'a', 't', 'e', ':', 'd', 'e', 'l', 'a', 'y'] {
        spec_parse_u64(tags@[i].1@)
    } else {
        spec_delay(tags, i + 1)
    }
}

pub open spec fn spec_parse_u64(s: Seq<char>) -> Option<u64> {
    if s.len() == 0 { None } else { spec_parse_acc(s, 0, 0) }
}

pub open spec fn spec_parse_acc(s: Seq<char>, i: int, acc: nat) -> Option<u64>
    decreases s.len() - i,
{
    if i >= s.len() {
        Some(acc as u64)
    } else if s[i] < '0' || s[i] > '9' {
        None
    } else {
        let n = acc * 10 + ((s[i] as u64) - ('0' as u64)) as nat;
        if n > (u64::MAX as nat) { None } else { spec_parse_acc(s, i + 1, n) }
    }
}

pub open spec fn spec_promise_get(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, spec_promise_res(404, None))
    } else {
        let obj = spec_project_obj(map[id@], now);
        (doc, spec_promise_res(200, Some(spec_record(id, obj.promise))))
    }
}

pub open spec fn spec_new_obj(timeout_at: u64, now: Time, param: Value, tags: Tags, runnable: bool) -> ObjV {
    let live = timeout_at > now;
    let promise = PromV {
        state: if live { PromiseState::Pending } else if spec_timer(tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
        param,
        value: spec_empty_value(),
        tags,
        timeout_at,
        created_at: if live { now } else { timeout_at },
        settled_at: if live { None } else { Some(timeout_at) },
        callbacks: Seq::empty(),
        listeners: Seq::empty(),
    };
    let task = if runnable {
        Some(TkV {
            state: if live { TaskState::Pending } else { TaskState::Fulfilled },
            version: 0,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: if live { Some(now) } else { None },
            resumes: Seq::empty(),
        })
    } else {
        None
    };
    ObjV { promise, task }
}

pub open spec fn spec_promise_create(doc: DocumentBodyV, req: PromiseCreateReq, now: Time) -> (DocumentBodyV, Response) {
    if req.timeout_at > MAX_TIME || (spec_timer(req.tags) && spec_targeted(req.tags)) {
        (doc, spec_promise_res(400, None))
    } else {
        let map = spec_workflow_map(doc);
        if map.contains_key(req.id@) {
            let obj = spec_project_obj(map[req.id@], now);
            (doc, spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        } else {
            let obj = spec_new_obj(req.timeout_at, now, req.param, req.tags, spec_targeted(req.tags));
            (spec_with_workflow(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
        }
    }
}

pub open spec fn spec_promise_settle(doc: DocumentBodyV, req: PromiseSettleReq, now: Time) -> (DocumentBodyV, Response) {
    if !req.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
        if !map.contains_key(req.id@) {
            (doc, spec_promise_res(404, None))
        } else {
            let seen = spec_project_obj(map[req.id@], now);
            if seen.promise.state != PromiseState::Pending {
                (doc, spec_promise_res(200, Some(spec_record(req.id, seen.promise))))
            } else {
                let promise = PromV { state: req.state, value: req.value, settled_at: Some(now), ..seen.promise };
                let task = match seen.task {
                    Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)),
                    other => other,
                };
                let obj = ObjV { promise, task };
                (spec_with_workflow(doc, map.insert(req.id@, obj)), spec_promise_res(200, Some(spec_record(req.id, obj.promise))))
            }
        }
    }
}

pub open spec fn spec_register_callback(doc: DocumentBodyV, awaited: String, awaiter: String, now: Time) -> (DocumentBodyV, Response) {
    if awaited@ == awaiter@ || !same_origin_spec(awaited@, awaiter@) {
        (doc, spec_promise_res(400, None))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
        if !map.contains_key(awaited@) {
            (doc, spec_promise_res(404, None))
        } else if !map.contains_key(awaiter@) {
            (doc, spec_promise_res(422, None))
        } else {
            let awaited_obj = spec_project_obj(map[awaited@], now);
            let awaiter_obj = spec_project_obj(map[awaiter@], now);
            if !spec_targeted(awaiter_obj.promise.tags) || !spec_awaitable(awaited_obj.promise.tags) {
                (doc, spec_promise_res(422, None))
            } else {
                let res = spec_promise_res(200, Some(spec_record(awaited, awaited_obj.promise)));
                if awaited_obj.promise.state == PromiseState::Pending && awaiter_obj.promise.state == PromiseState::Pending {
                    let callbacks = if awaited_obj.promise.callbacks.contains(awaiter@) {
                        awaited_obj.promise.callbacks
                    } else {
                        awaited_obj.promise.callbacks.push(awaiter@)
                    };
                    let awaited_obj = ObjV { promise: PromV { callbacks, ..awaited_obj.promise }, ..awaited_obj };
                    (spec_with_workflow(doc, map.insert(awaited@, awaited_obj)), res)
                } else {
                    (doc, res)
                }
            }
        }
    }
}

pub open spec fn spec_register_listener(doc: DocumentBodyV, awaited: String, address: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(awaited@) {
        (doc, spec_promise_res(404, None))
    } else {
        let obj = spec_project_obj(map[awaited@], now);
        if !spec_awaitable(obj.promise.tags) {
            (doc, spec_promise_res(422, None))
        } else {
            let res = spec_promise_res(200, Some(spec_record(awaited, obj.promise)));
            if obj.promise.state == PromiseState::Pending {
                let listeners = if obj.promise.listeners.contains(address@) {
                    obj.promise.listeners
                } else {
                    obj.promise.listeners.push(address@)
                };
                let obj = ObjV { promise: PromV { listeners, ..obj.promise }, ..obj };
                (spec_with_workflow(doc, map.insert(awaited@, obj)), res)
            } else {
                (doc, res)
            }
        }
    }
}

pub open spec fn spec_task_get(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::TaskGet(TaskGetRes { status: 404, task: None }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::TaskGet(TaskGetRes { status: 404, task: None })),
            Some(t) => (doc, Response::TaskGet(TaskGetRes { status: 200, task: Some(spec_task_record(id, t)) })),
        }
    }
}

pub open spec fn spec_acquire(t: TkV, pid: Seq<char>, ttl: u64, now: Time) -> TkV {
    TkV {
        state: TaskState::Acquired,
        version: spec_sat_add(t.version, 1),
        pid: Some(pid),
        ttl: Some(ttl),
        lease_timeout_at: Some(spec_sat_add(now, ttl)),
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_task_create(doc: DocumentBodyV, pid: String, ttl: u64, action: PromiseCreateReq, now: Time) -> (DocumentBodyV, Response) {
    if ttl == 0 || ttl > MAX_TIME || action.timeout_at > MAX_TIME
        || !spec_targeted(action.tags) || spec_timer(action.tags) {
        (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
    } else {
        let (doc, created) = spec_promise_create(doc, action, now);
        match created {
            Response::Promise(inner) if inner.status == 400 => {
                (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
            },
            _ => {
                let map = spec_workflow_map(doc);
                if !map.contains_key(action.id@) {
                    (doc, Response::TaskClaim(TaskClaimRes { status: 422, task: None, promise: None }))
                } else {
                    let seen = spec_project_obj(map[action.id@], now);
                    if !spec_targeted(seen.promise.tags) {
                        (doc, Response::TaskClaim(TaskClaimRes { status: 422, task: None, promise: None }))
                    } else {
                        match seen.task {
                            None => (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None })),
                            Some(t) if t.state == TaskState::Fulfilled => (
                                doc,
                                Response::TaskClaim(TaskClaimRes {
                                    status: 200,
                                    task: Some(spec_task_record(action.id, t)),
                                    promise: Some(spec_record(action.id, seen.promise)),
                                }),
                            ),
                            Some(t) if t.state == TaskState::Pending && t.version >= MAX_VERSION => {
                                (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None }))
                            },
                            Some(t) if t.state == TaskState::Pending => {
                                let u = spec_acquire(t, pid@, ttl, now);
                                let obj = ObjV { task: Some(u), ..seen };
                                (
                                    spec_with_workflow(doc, map.insert(action.id@, obj)),
                                    Response::TaskClaim(TaskClaimRes {
                                        status: 200,
                                        task: Some(spec_task_record(action.id, u)),
                                        promise: Some(spec_record(action.id, obj.promise)),
                                    }),
                                )
                            },
                            _ => (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None })),
                        }
                    }
                }
            },
        }
    }
}

pub enum Held { Ok(ObjV), Missing, Stale }

pub open spec fn spec_held(map: Map<Seq<char>, ObjV>, id: Seq<char>, version: u64, now: Time) -> (Map<Seq<char>, ObjV>, Held) {
    if !map.contains_key(id) {
        (map, Held::Missing)
    } else {
        let obj = spec_project_obj(map[id], now);
        match obj.task {
            None => (map, Held::Missing),
            Some(t) if t.state == TaskState::Acquired && t.version == version && obj.promise.state == PromiseState::Pending => (map, Held::Ok(obj)),
            _ => (map, Held::Stale),
        }
    }
}

pub open spec fn spec_task_acquire(doc: DocumentBodyV, id: String, version: u64, pid: String, ttl: u64, now: Time) -> (DocumentBodyV, Response) {
    if ttl == 0 || ttl > MAX_TIME {
        (doc, Response::TaskClaim(TaskClaimRes { status: 400, task: None, promise: None }))
    } else {
        let doc = spec_opened(doc);
        let map = spec_workflow_map(doc);
        if !map.contains_key(id@) {
            (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None }))
        } else {
            let obj = spec_project_obj(map[id@], now);
            match obj.task {
                None => (doc, Response::TaskClaim(TaskClaimRes { status: 404, task: None, promise: None })),
                Some(t) if t.state != TaskState::Pending || t.version != version
                    || obj.promise.state != PromiseState::Pending || t.version >= MAX_VERSION => {
                    (doc, Response::TaskClaim(TaskClaimRes { status: 409, task: None, promise: None }))
                },
                Some(t) => {
                    let u = spec_acquire(t, pid@, ttl, now);
                    let obj = ObjV { task: Some(u), ..obj };
                    (
                        spec_with_workflow(doc, map.insert(id@, obj)),
                        Response::TaskClaim(TaskClaimRes {
                            status: 200,
                            task: Some(spec_task_record(id, u)),
                            promise: Some(spec_record(id, obj.promise)),
                        }),
                    )
                },
            }
        }
    }
}

pub open spec fn spec_unlease(t: TkV, state: TaskState, retry: Option<u64>) -> TkV {
    TkV { state, pid: None, ttl: None, lease_timeout_at: None, retry_timeout_at: retry, ..t }
}

pub open spec fn spec_task_release(doc: DocumentBodyV, id: String, version: u64, now: Time) -> (DocumentBodyV, Response) {
    let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(obj) => {
            let task = match obj.task { Some(t) => Some(spec_unlease(t, TaskState::Pending, Some(now))), None => None };
            (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
        },
    }
}

pub open spec fn spec_task_fulfill(doc: DocumentBodyV, id: String, version: u64, action: PromiseSettleReq, now: Time) -> (DocumentBodyV, Response) {
    if !action.state.spec_settable() {
        (doc, spec_promise_res(400, None))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), spec_promise_res(404, None)),
            Held::Stale => (spec_with_workflow(doc, map), spec_promise_res(409, None)),
            Held::Ok(obj) => {
                let promise = PromV { state: action.state, value: action.value, settled_at: Some(now), ..obj.promise };
                let task = match obj.task { Some(t) if t.state != TaskState::Fulfilled => Some(spec_fulfill_task(t)), other => other };
                let obj = ObjV { promise, task };
                (spec_with_workflow(doc, map.insert(id@, obj)), spec_promise_res(200, Some(spec_record(id, obj.promise))))
            },
        }
    }
}

pub open spec fn spec_task_halt(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::Status(StatusRes { status: 404 }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::Status(StatusRes { status: 404 })),
            Some(t) if t.state == TaskState::Fulfilled => (doc, Response::Status(StatusRes { status: 409 })),
            Some(t) if t.state == TaskState::Halted => (doc, Response::Status(StatusRes { status: 200 })),
            Some(t) => {
                let obj = ObjV { task: Some(spec_unlease(t, TaskState::Halted, None)), ..obj };
                (spec_with_workflow(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_task_continue(doc: DocumentBodyV, id: String, now: Time) -> (DocumentBodyV, Response) {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if !map.contains_key(id@) {
        (doc, Response::Status(StatusRes { status: 404 }))
    } else {
        let obj = spec_project_obj(map[id@], now);
        match obj.task {
            None => (doc, Response::Status(StatusRes { status: 404 })),
            Some(t) if t.state != TaskState::Halted || obj.promise.state != PromiseState::Pending => {
                (doc, Response::Status(StatusRes { status: 409 }))
            },
            Some(t) => {
                let obj = ObjV { task: Some(TkV { state: TaskState::Pending, retry_timeout_at: Some(now), ..t }), ..obj };
                (spec_with_workflow(doc, map.insert(id@, obj)), Response::Status(StatusRes { status: 200 }))
            },
        }
    }
}

pub open spec fn spec_heartbeat(doc: DocumentBodyV, pid: String, tasks: Seq<TaskRef>, now: Time) -> (DocumentBodyV, Response) {
    if tasks.len() == 0 {
        (doc, Response::Status(StatusRes { status: 200 }))
    } else if !spec_one_origin(tasks, origin(tasks[0].id@), 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        (spec_with_workflow(doc, spec_extend(spec_workflow_map(doc), pid@, tasks, now, 0)), Response::Status(StatusRes { status: 200 }))
    }
}

pub open spec fn spec_one_origin(tasks: Seq<TaskRef>, origin_chars: Seq<char>, i: int) -> bool
    decreases tasks.len() - i,
{
    if i < 0 || i >= tasks.len() { true }
    else { origin(tasks[i].id@) == origin_chars && spec_one_origin(tasks, origin_chars, i + 1) }
}

pub open spec fn spec_extend(map: Map<Seq<char>, ObjV>, pid: Seq<char>, tasks: Seq<TaskRef>, now: Time, i: int) -> Map<Seq<char>, ObjV>
    decreases tasks.len() - i,
{
    if i < 0 || i >= tasks.len() {
        map
    } else if !map.contains_key(tasks[i].id@) {
        spec_extend(map, pid, tasks, now, i + 1)
    } else {
        let obj = spec_project_obj(map[tasks[i].id@], now);
        match obj.task {
            Some(t) if t.state == TaskState::Acquired && t.version == tasks[i].version && t.pid == Some(pid) => {
                let ttl = match t.ttl { Some(n) => n, None => 0 };
                let at = spec_sat_add(now, ttl);
                let obj = ObjV { task: Some(TkV { lease_timeout_at: Some(at), ..t }), ..obj };
                spec_extend(map.insert(tasks[i].id@, obj), pid, tasks, now, i + 1)
            },
            _ => spec_extend(map, pid, tasks, now, i + 1),
        }
    }
}

pub open spec fn spec_suspend(doc: DocumentBodyV, id: String, version: u64, actions: Seq<PromiseRegisterCallbackReq>, now: Time) -> (DocumentBodyV, Response) {
    if actions.len() == 0 || spec_bad_suspend(actions, id@, 0) || !spec_distinct_awaited(actions, 0) {
        (doc, Response::Status(StatusRes { status: 400 }))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
            Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
            Held::Ok(obj) => {
                if spec_missing_awaited(map, actions, 0) || spec_unawaitable(map, actions, 0) {
                    (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 422 }))
                } else if spec_any_settled(map, actions, now, 0) {
                    let task = match obj.task { Some(t) => Some(TkV { resumes: Seq::empty(), ..t }), None => None };
                    (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 300 }))
                } else {
                    let map = spec_add_callbacks(map, id@, actions, 0);
                    let obj = map[id@];
                    let task = match obj.task {
                        Some(t) => Some(TkV { resumes: Seq::empty(), ..spec_unlease(t, TaskState::Suspended, None) }),
                        None => None,
                    };
                    (spec_with_workflow(doc, map.insert(id@, ObjV { task, ..obj })), Response::Status(StatusRes { status: 200 }))
                }
            },
        }
    }
}

pub open spec fn spec_bad_suspend(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else { actions[i].awaited@ == id || !same_origin_spec(actions[i].awaited@, id) || spec_bad_suspend(actions, id, i + 1) }
}

pub open spec fn spec_distinct_awaited(actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { true }
    else { !spec_seen(actions, actions[i].awaited@, 0, i) && spec_distinct_awaited(actions, i + 1) }
}

pub open spec fn spec_seen(actions: Seq<PromiseRegisterCallbackReq>, id: Seq<char>, j: int, stop: int) -> bool
    decreases stop - j,
{
    if j < 0 || j >= stop || j >= actions.len() { false }
    else { actions[j].awaited@ == id || spec_seen(actions, id, j + 1, stop) }
}

pub open spec fn spec_missing_awaited(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else { !map.contains_key(actions[i].awaited@) || spec_missing_awaited(map, actions, i + 1) }
}

pub open spec fn spec_unawaitable(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else {
        (map.contains_key(actions[i].awaited@) && !spec_awaitable(map[actions[i].awaited@].promise.tags))
            || spec_unawaitable(map, actions, i + 1)
    }
}

pub open spec fn spec_any_settled(map: Map<Seq<char>, ObjV>, actions: Seq<PromiseRegisterCallbackReq>, now: Time, i: int) -> bool
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { false }
    else {
        (map.contains_key(actions[i].awaited@) && spec_project_obj(map[actions[i].awaited@], now).promise.state != PromiseState::Pending)
            || spec_any_settled(map, actions, now, i + 1)
    }
}

pub open spec fn spec_add_callbacks(map: Map<Seq<char>, ObjV>, id: Seq<char>, actions: Seq<PromiseRegisterCallbackReq>, i: int) -> Map<Seq<char>, ObjV>
    decreases actions.len() - i,
{
    if i < 0 || i >= actions.len() { map }
    else if !map.contains_key(actions[i].awaited@) {
        spec_add_callbacks(map, id, actions, i + 1)
    } else {
        let obj = map[actions[i].awaited@];
        let callbacks = if obj.promise.callbacks.contains(id) { obj.promise.callbacks } else { obj.promise.callbacks.push(id) };
        let obj = ObjV { promise: PromV { callbacks, ..obj.promise }, ..obj };
        spec_add_callbacks(map.insert(actions[i].awaited@, obj), id, actions, i + 1)
    }
}

pub open spec fn spec_fence(doc: DocumentBodyV, id: String, version: u64, action: TaskFenceAction, now: Time) -> (DocumentBodyV, Response) {
    let target = match action {
        TaskFenceAction::Create(c) => c.id,
        TaskFenceAction::Settle(st) => st.id,
    };
    if target@ == id@ || !same_origin_spec(target@, id@) {
        (doc, Response::TaskFence(TaskFenceRes { status: 400, action: None }))
    } else {
        let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
        match held {
            Held::Missing => (spec_with_workflow(doc, map), Response::TaskFence(TaskFenceRes { status: 404, action: None })),
            Held::Stale => (spec_with_workflow(doc, map), Response::TaskFence(TaskFenceRes { status: 409, action: None })),
            Held::Ok(_) => {
                let doc = spec_with_workflow(doc, map);
                match action {
                    TaskFenceAction::Create(req) => {
                        let (doc, response) = spec_promise_create(doc, req, now);
                        let inner = match response { Response::Promise(p) => p, _ => PromiseRes { status: 500, promise: None } };
                        (doc, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Create(inner)) }))
                    },
                    TaskFenceAction::Settle(req) => {
                        let (doc, response) = spec_promise_settle(doc, req, now);
                        let inner = match response { Response::Promise(p) => p, _ => PromiseRes { status: 500, promise: None } };
                        (doc, Response::TaskFence(TaskFenceRes { status: 200, action: Some(TaskFenceInnerRes::Settle(inner)) }))
                    },
                }
            },
        }
    }
}

pub open spec fn spec_fence_check(doc: DocumentBodyV, id: String, version: u64, now: Time) -> (DocumentBodyV, Response) {
    let (map, held) = spec_held(spec_workflow_map(doc), id@, version, now);
    match held {
        Held::Missing => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 404 })),
        Held::Stale => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 409 })),
        Held::Ok(_) => (spec_with_workflow(doc, map), Response::Status(StatusRes { status: 200 })),
    }
}

pub open spec fn spec_schedule_get(doc: DocumentBodyV, id: String) -> (DocumentBodyV, Response) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.id == id => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
        _ => (doc, Response::Schedule(ScheduleRes { status: 404, schedule: None })),
    }
}

pub open spec fn spec_schedule_create(doc: DocumentBodyV, req: ScheduleCreateReq, now: Time) -> (DocumentBodyV, Response) {
    if now > MAX_TIME {
        (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }))
    } else {
        let next_run_at = echod_abstract::trusted::spec_next_cron(req.cron@, now);
        if !spec_deadline_bounded(next_run_at, req.promise_timeout)
        || (spec_targeted(req.promise_tags) && spec_timer(req.promise_tags))
        {
            (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }))
        } else {
            match doc {
                DocumentBodyV::Schedule(Some(schedule)) => (doc, Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) })),
                _ => {
                    let schedule = Schedule {
                        id: req.id,
                        cron: req.cron,
                        promise_id: req.promise_id,
                        promise_timeout: req.promise_timeout,
                        promise_param: req.promise_param,
                        promise_tags: req.promise_tags,
                        next_run_at,
                        last_run_at: None,
                        created_at: now,
                    };
                    (DocumentBodyV::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(schedule) }))
                },
            }
        }
    }
}

pub open spec fn spec_schedule_delete(doc: DocumentBodyV, id: String) -> (DocumentBodyV, Response) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.id == id => (DocumentBodyV::Schedule(None), Response::Status(StatusRes { status: 200 })),
        _ => (doc, Response::Status(StatusRes { status: 404 })),
    }
}

pub open spec fn spec_fire_schedule(doc: DocumentBodyV, now: Time) -> (DocumentBodyV, Seq<PendingV>) {
    match doc {
        DocumentBodyV::Schedule(Some(schedule))
            if schedule.next_run_at <= now
                && schedule.next_run_at <= MAX_TIME
                && spec_deadline_bounded(
                    schedule.next_run_at,
                    schedule.promise_timeout,
                ) => {
            let at = schedule.next_run_at;
            let promise = echod_abstract::trusted::spec_expand(
                schedule.promise_id@,
                schedule.id@,
                at,
            );
            if promise.len() > usize::MAX as int
                || !(exists|carrier: String| carrier@ == promise)
            {
                (doc, Seq::empty())
            } else {
                let pending = PendingV {
                    promise,
                    at,
                    timeout: schedule.promise_timeout,
                    param: schedule.promise_param,
                    tags: schedule.promise_tags,
                };
                let schedule = Schedule {
                    last_run_at: Some(at),
                    next_run_at: echod_abstract::trusted::spec_next_cron(schedule.cron@, at),
                    ..schedule
                };
                (DocumentBodyV::Schedule(Some(schedule)), seq![pending])
            }
        },
        other => (other, Seq::empty()),
    }
}

pub open spec fn spec_project_due_object(
    obj: ObjV,
    now: Time,
    retry_timeout: u64,
) -> ObjV {
    if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
        spec_project_obj(obj, now)
    } else if obj.promise.state == PromiseState::Pending {
        match obj.task {
            Some(t) if t.state == TaskState::Acquired
                && match t.lease_timeout_at { Some(at) => at <= now, None => false } => {
                let task = spec_unlease(t, TaskState::Pending, Some(now));
                ObjV {
                    task: Some(TkV {
                        retry_timeout_at: Some(spec_sat_add(now, retry_timeout)),
                        ..task
                    }),
                    ..obj
                }
            },
            Some(t) if t.state == TaskState::Pending
                && match t.retry_timeout_at { Some(at) => at <= now, None => false } => {
                ObjV {
                    task: Some(TkV {
                        retry_timeout_at: Some(spec_sat_add(now, retry_timeout)),
                        ..t
                    }),
                    ..obj
                }
            },
            _ => obj,
        }
    } else {
        obj
    }
}

pub open spec fn spec_project_keys(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV>
    decreases count,
{
    if count == 0 {
        map
    } else {
        let prior = spec_project_keys(map, keys, (count - 1) as nat, now, retry_timeout);
        let id = keys[count as int - 1];
        if prior.contains_key(id) {
            prior.insert(id, spec_project_due_object(prior[id], now, retry_timeout))
        } else {
            prior
        }
    }
}

pub open spec fn spec_project_workflow(
    map: Map<Seq<char>, ObjV>,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV> {
    let keys = spec_sorted_present(map);
    spec_project_keys(map, keys, keys.len(), now, retry_timeout)
}

pub open spec fn spec_resume_callbacks(
    map: Map<Seq<char>, ObjV>,
    callbacks: Seq<Seq<char>>,
    count: nat,
    awaited: Seq<char>,
    since: Time,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV>
    decreases count,
{
    if count == 0 {
        map
    } else {
        let prior = spec_resume_callbacks(
            map,
            callbacks,
            (count - 1) as nat,
            awaited,
            since,
            now,
            retry_timeout,
        );
        spec_resume(
            prior,
            callbacks[count as int - 1],
            awaited,
            since,
            now,
            retry_timeout,
        )
    }
}

pub open spec fn spec_drain_settled_callbacks(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(id)
        || map[id].promise.state == PromiseState::Pending
    {
        map
    } else {
        spec_drain_callbacks(
            map,
            id,
            map[id].promise.callbacks.len(),
            now,
            retry_timeout,
        )
    }
}

pub open spec fn spec_drain_callback_keys(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV>
    decreases count,
{
    if count == 0 {
        map
    } else {
        let prior = spec_drain_callback_keys(
            map,
            keys,
            (count - 1) as nat,
            now,
            retry_timeout,
        );
        spec_drain_settled_callbacks(
            prior,
            keys[count as int - 1],
            now,
            retry_timeout,
        )
    }
}

pub open spec fn spec_clear_settled_listeners(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(id)
        || map[id].promise.state == PromiseState::Pending
    {
        map
    } else {
        let object = map[id];
        map.insert(id, ObjV {
            promise: PromV {
                listeners: Seq::empty(),
                ..object.promise
            },
            ..object
        })
    }
}

pub open spec fn spec_clear_listener_keys(
    map: Map<Seq<char>, ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
) -> Map<Seq<char>, ObjV>
    decreases count,
{
    if count == 0 {
        map
    } else {
        spec_clear_settled_listeners(
            spec_clear_listener_keys(
                map, keys, (count - 1) as nat,
            ),
            keys[count as int - 1],
        )
    }
}

pub open spec fn spec_drain_callbacks(
    map: Map<Seq<char>, ObjV>,
    id: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV>
    decreases count,
{
    if count == 0 {
        map
    } else {
        let prior =
            spec_drain_callbacks(
                map, id, (count - 1) as nat, now, retry_timeout,
            );
        if !prior.contains_key(id)
            || prior[id].promise.callbacks.len() == 0
        {
            prior
        } else {
            let obj = prior[id];
            let awaiter = obj.promise.callbacks[0];
            let since =
                match obj.promise.settled_at { Some(at) => at, None => 0 };
            let popped = prior.insert(id, ObjV {
                promise: PromV {
                    callbacks: obj.promise.callbacks.skip(1),
                    ..obj.promise
                },
                ..obj
            });
            spec_resume(
                popped, awaiter, id, since, now, retry_timeout,
            )
        }
    }
}

pub open spec fn spec_drain_workflow(
    map: Map<Seq<char>, ObjV>,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV> {
    let keys = spec_sorted_present(map);
    let resumed = spec_drain_callback_keys(
        map, keys, keys.len(), now, retry_timeout,
    );
    spec_clear_listener_keys(resumed, keys, keys.len())
}

/// The atomic two-phase workflow transition.
pub open spec fn spec_sweep(
    doc: DocumentBodyV,
    now: Time,
    retry_timeout: u64,
) -> (DocumentBodyV, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Workflow(map) => {
            let projected = spec_project_workflow(map, now, retry_timeout);
            let drained =
                spec_drain_workflow(projected, now, retry_timeout);
            let after = DocumentBodyV::Workflow(drained);
            (after, Seq::empty(), spec_committed_notes(doc, after, now))
        },
        _ => (doc, Seq::empty(), Seq::empty()),
    }
}

pub open spec fn spec_due_transition(
    doc: DocumentBodyV,
    now: Time,
    retry_timeout: u64,
) -> (DocumentBodyV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Schedule(_) => {
            let (next, born) = spec_fire_schedule(doc, now);
            (next, None, born, Seq::empty())
        },
        DocumentBodyV::Workflow(_) => {
            let (next, born, notes) = spec_sweep(doc, now, retry_timeout);
            (next, None, born, notes)
        },
    }
}

pub open spec fn spec_request_transition(
    doc: DocumentBodyV,
    request: Request,
    now: Time,
    retry_timeout: u64,
) -> (DocumentBodyV, Response, Seq<PendingV>, Seq<NoteV>) {
    match doc {
        DocumentBodyV::Schedule(_) => {
            let (doc, response) = spec_handle(doc, request, now);
            (doc, response, Seq::empty(), Seq::empty())
        },
        DocumentBodyV::Workflow(_) => {
            let (swept, before_born, before_notes) =
                spec_sweep(doc, now, retry_timeout);
            let (handled, response) = spec_handle(swept, request, now);
            let (closed, after_born, after_notes) =
                spec_sweep(handled, now, retry_timeout);
            (
                closed,
                response,
                before_born + after_born,
                spec_committed_notes(doc, closed, now),
            )
        },
    }
}

pub open spec fn spec_occurrence(doc: DocumentBodyV, pending: PendingV, now: Time) -> DocumentBodyV {
    let doc = spec_opened(doc);
    let map = spec_workflow_map(doc);
    if map.contains_key(pending.promise) || now < pending.at {
        doc
    } else {
        let timeout_at = spec_sat_add(pending.at, pending.timeout);
        let born = spec_new_obj(timeout_at, now, pending.param, pending.tags, spec_targeted(pending.tags) && !spec_timer(pending.tags));
        let promise = if timeout_at > pending.at {
            PromV { created_at: pending.at, ..born.promise }
        } else {
            born.promise
        };
        let task = match born.task {
            Some(t) if t.state == TaskState::Pending => Some(TkV { retry_timeout_at: Some(now), ..t }),
            other => other,
        };
        spec_with_workflow(doc, map.insert(pending.promise, ObjV { promise, task }))
    }
}

/// The atomic document transition used by production schedule firing.
///
/// Existing due work is closed before insertion.  The post-insert closure
/// offers a live runnable occurrence immediately, advancing its retry slot to
/// `now + retry_timeout`; an already expired occurrence is born settled and
/// therefore emits no stale Execute.
pub open spec fn spec_occurrence_transition(
    doc: DocumentBodyV,
    pending: PendingV,
    now: Time,
    retry_timeout: u64,
) -> (DocumentBodyV, Seq<NoteV>) {
    let (before, _, _) = spec_sweep(doc, now, retry_timeout);
    let created = spec_occurrence(before, pending, now);
    let (after, _, _) = spec_sweep(created, now, retry_timeout);
    (after, spec_committed_notes(doc, after, now))
}

pub open spec fn spec_sorted_present(map: Map<Seq<char>, ObjV>) -> Seq<Seq<char>> {
    spec_sorted(map.dom())
}

/// Opaque: the choice is read through `timers::lemma_min_key` alone.
#[verifier::opaque]
pub open spec fn spec_min_key(keys: Set<Seq<char>>) -> Seq<char> {
    choose|k: Seq<char>| keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k)
}

pub open spec fn spec_sorted(keys: Set<Seq<char>>) -> Seq<Seq<char>>
    decreases keys.len(),
    via spec_sorted_decreases
{
    if !keys.finite() || keys.len() == 0 { Seq::empty() }
    else {
        let k = spec_min_key(keys);
        seq![k] + spec_sorted(keys.remove(k))
    }
}

#[via_fn]
proof fn spec_sorted_decreases(keys: Set<Seq<char>>) {
    if keys.finite() && keys.len() > 0 {
        crate::timers::lemma_min_key(keys);
    }
}

pub open spec fn spec_earlier(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

pub open spec fn spec_promise_due(obj: ObjV, now: Time) -> Option<u64> {
    if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
        Some(obj.promise.timeout_at)
    } else if obj.promise.state != PromiseState::Pending
        && (obj.promise.callbacks.len() > 0 || obj.promise.listeners.len() > 0)
    {
        let at = match obj.promise.settled_at { Some(t) => t, None => 0 };
        if at <= now { Some(at) } else { None }
    } else {
        None
    }
}

pub open spec fn spec_lease_due(obj: ObjV, now: Time) -> Option<u64> {
    match obj.task {
        Some(t) if obj.promise.state == PromiseState::Pending && t.state == TaskState::Acquired => match t.lease_timeout_at {
            Some(at) if at <= now => Some(at),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn spec_retry_due(obj: ObjV, now: Time) -> Option<u64> {
    match obj.task {
        Some(t) if obj.promise.state == PromiseState::Pending && t.state == TaskState::Pending => match t.retry_timeout_at {
            Some(at) if at <= now => Some(at),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn spec_obj_due(obj: ObjV, now: Time) -> Option<u64> {
    spec_earlier(spec_earlier(spec_promise_due(obj, now), spec_lease_due(obj, now)), spec_retry_due(obj, now))
}

/// `resume`: a suspended awaiter is offered again from `since`, the instant
/// the awaited promise settled. The awaiter is read through its projection
/// at `now`: a task whose own promise is settled reads as fulfilled.
pub open spec fn spec_resume(
    map: Map<Seq<char>, ObjV>,
    awaiter: Seq<char>,
    awaited: Seq<char>,
    since: Time,
    now: Time,
    retry_timeout: u64,
) -> Map<Seq<char>, ObjV> {
    if !map.contains_key(awaiter) {
        map
    } else {
        match spec_project_obj(map[awaiter], now).task {
            None => map,
            Some(t) => match t.state {
                TaskState::Suspended => map.insert(awaiter, ObjV {
                    task: Some(TkV {
                        state: TaskState::Pending,
                        pid: None,
                        ttl: None,
                        lease_timeout_at: None,
                    retry_timeout_at: Some(
                        spec_sat_add(now, retry_timeout),
                    ),
                        resumes: seq![awaited],
                        ..t
                    }),
                    ..map[awaiter]
                }),
                TaskState::Fulfilled => map,
                _ => if t.resumes.contains(awaited) {
                    map
                } else {
                    map.insert(awaiter, ObjV { task: Some(TkV { resumes: t.resumes.push(awaited), ..t }), ..map[awaiter] })
                },
            },
        }
    }
}

pub open spec fn spec_wake(node: NodeV) -> Option<nat> {
    if node.flight is Some { None } else { spec_next(node) }
}

pub open spec fn spec_next(node: NodeV) -> Option<nat> {
    let from_pending = if node.pending.len() == 0 { None } else { Some(node.pending[0].at as nat) };
    spec_min_nat(from_pending, spec_deadlines(node, node.documents, 0))
}

pub open spec fn spec_min_nat(a: Option<nat>, b: Option<nat>) -> Option<nat> {
    match (a, b) {
        (None, other) => other,
        (other, None) => other,
        (Some(x), Some(y)) => Some(if x < y { x } else { y }),
    }
}

pub open spec fn spec_deadlines(node: NodeV, docs: Seq<CachedV>, i: int) -> Option<nat>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        None
    } else if !spec_owns(node, docs[i].key) {
        spec_deadlines(node, docs, i + 1)
    } else {
        spec_min_nat(spec_body_deadline(spec_read(docs[i].key, docs[i].body)), spec_deadlines(node, docs, i + 1))
    }
}

pub open spec fn spec_body_deadline(doc: DocumentBodyV) -> Option<nat> {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) => Some(schedule.next_run_at as nat),
        DocumentBodyV::Workflow(map) => spec_map_deadline(map, spec_sorted(map.dom())),
        DocumentBodyV::Schedule(None) => None,
    }
}

pub open spec fn spec_map_deadline(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>) -> Option<nat>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else { spec_min_nat(spec_obj_deadline(map[keys[0]]), spec_map_deadline(map, keys.drop_first())) }
}

pub open spec fn spec_obj_deadline(obj: ObjV) -> Option<nat> {
    match spec_obj_due(obj, u64::MAX) {
        Some(at) => Some(at as nat),
        None => None,
    }
}

pub open spec fn spec_earliest_key(node: NodeV, now: Time) -> Option<Seq<char>> {
    spec_earliest_from(node, node.documents, 0, now, None)
}

pub open spec fn spec_earliest_from(node: NodeV, docs: Seq<CachedV>, i: int, now: Time, best: Option<(u64, Seq<char>)>) -> Option<Seq<char>>
    decreases docs.len() - i,
{
    if i < 0 || i >= docs.len() {
        match best { Some((_, key)) => Some(key), None => None }
    } else if !spec_owns(node, docs[i].key) {
        spec_earliest_from(node, docs, i + 1, now, best)
    } else {
        match spec_earliest_in(spec_read(docs[i].key, docs[i].body), now) {
            Some(at) => {
                let better = match best { None => true, Some((b, _)) => at < b };
                let best = if better { Some((at, docs[i].key)) } else { best };
                spec_earliest_from(node, docs, i + 1, now, best)
            },
            None => spec_earliest_from(node, docs, i + 1, now, best),
        }
    }
}

pub open spec fn spec_earliest_in(doc: DocumentBodyV, now: Time) -> Option<u64> {
    match doc {
        DocumentBodyV::Schedule(Some(schedule)) if schedule.next_run_at <= now => Some(schedule.next_run_at),
        DocumentBodyV::Workflow(map) => spec_map_due(map, spec_sorted(map.dom()), now),
        _ => None,
    }
}

pub open spec fn spec_map_due(map: Map<Seq<char>, ObjV>, keys: Seq<Seq<char>>, now: Time) -> Option<u64>
    decreases keys.len(),
{
    if keys.len() == 0 { None }
    else { spec_earlier(spec_obj_due(map[keys[0]], now), spec_map_due(map, keys.drop_first(), now)) }
}

}
