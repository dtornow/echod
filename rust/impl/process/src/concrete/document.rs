//! Executable concrete document machine and legacy Rover node. A request or a due document is a flight: load the document,
//! decide, write it back, then answer. The store keeps the bytes. Nothing
//! here calls the abstract model.
//!
//! The executable node first, inside `verus!`, each function carrying the
//! `spec_*` twin it computes; then the node as a specification, over the
//! view types: `NodeV`, `DocV`, the `spec_*` twins of its handlers and steps.
//!
//! Trusted here: the JSON codec computes `spec_encode` / `spec_read`
//! (`encode`, `decode`), the key hash computes `spec_fnv` (`hash_key`, over
//! the store's `fnv1a`), a string is its characters (`chars_of`), a copy of a
//! sorted table is that table (`Objects::clone`), and the cron engine and the
//! id template are the abstract crate's `next_cron` and `expand`. Everything
//! else Verus checks: `Node::step` computes `spec_node`, and `Node::new`
//! computes `spec_initial_node`.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]

use vstd::pervasive::VecAdditionalExecFns;
use vstd::prelude::*;

use echod_concrete_spec::node::*;

use echod_types::{
    origin_of, same_origin, PromiseCreateReq, PromiseRecord, PromiseRegisterCallbackReq,
    PromiseRes, PromiseSettleReq, PromiseState, Request, Response, Schedule, ScheduleCreateReq,
    ScheduleRes, StatusRes, Tags, TaskClaimRes, TaskFenceAction, TaskFenceInnerRes, TaskFenceRes,
    TaskGetRes, TaskRecord, TaskRef, TaskState, Value,
};
#[cfg(not(verus_keep_ghost))]
use serde::{Deserialize, Serialize};

use crate::concrete::runtime::{expand, next_cron};
use crate::verified::runtime::copy;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::{axiom_string_ext, axiom_vec_ext};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::{lemma_tags_ext, lemma_value_ext};
use echod_abstract_spec::{Call, Dispatch, Output};
use rover_spec::rover::comm::ProcessEvent;
#[cfg(verus_keep_ghost)]
use rover_spec::rover::RoverSpec::StepResultV;
use rover_spec::rover::comm::Time;
#[cfg(verus_keep_ghost)]
use echod_types::{origin, same_origin_spec, AValue};

#[cfg(verus_keep_ghost)]
use echod_concrete_spec::model::{
    spec_bytes, spec_clock, spec_get, spec_initial_node, spec_node, spec_notes, spec_notify,
    spec_one, spec_reply, spec_string, Proc, LogicV,
};
use crate::concrete::rover::{Config, Logic, Message, Pid};
#[cfg(verus_keep_ghost)]
use echod_concrete_spec::store::{spec_before, spec_fnv, spec_sat_add, spec_starts};
use crate::concrete::store::{Read, StoreError};
use crate::concrete::store::{fnv1a, Etag, StoreCall, StoreOutcome};

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
    doc: Doc,
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
    decided: Option<Doc>,
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

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub enum Doc {
    Origin(Objects),
    Schedule(Option<Schedule>),
}

/// The objects of one origin, by id, in key order. The order is a type
/// invariant: every `Objects` Verus sees is sorted, so a lookup is a map
/// lookup and the first due object is the first in `spec_sorted`.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Objects {
    entries: Vec<(String, Obj)>,
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

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Obj {
    pub promise: Prom,
    pub task: Option<Tk>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Prom {
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
    pub callbacks: Vec<String>,
    pub listeners: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Serialize, Deserialize))]
pub struct Tk {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<String>,
    pub ttl: Option<u64>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Vec<String>,
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

spec fn spec_keys_of(entries: Seq<(String, Obj)>) -> Seq<Seq<char>> {
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

spec fn spec_sorted_entries(entries: Seq<(String, Obj)>) -> bool {
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

impl View for Doc {
    type V = DocV;
    closed spec fn view(&self) -> DocV {
        match self {
            Doc::Origin(objs) => DocV::Origin(objs@),
            Doc::Schedule(slot) => DocV::Schedule(*slot),
        }
    }
}

impl View for Pending {
    type V = PendingV;
    closed spec fn view(&self) -> PendingV {
        PendingV { promise: self.promise@, at: self.at, timeout: self.timeout, param: self.param, tags: self.tags }
    }
}

impl DeepView for Doc {
    type V = DocV;
    open spec fn deep_view(&self) -> DocV {
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
        CachedV { key: self.key@, body: spec_encode(self.doc@), etag: etag_v(self.etag) }
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
            decided: match self.decided { Some(doc) => Some(spec_encode(doc@)), None => None },
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
pub fn same_doc(a: &Doc, b: &Doc) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    match (a, b) {
        (Doc::Origin(x), Doc::Origin(y)) => same_objects(x, y),
        (Doc::Schedule(Some(x)), Doc::Schedule(Some(y))) => same_schedule(x, y),
        (Doc::Schedule(None), Doc::Schedule(None)) => true,
        _ => false,
    }
}

/// A copy of a document, equal to its source.
pub fn clone_doc(d: &Doc) -> (r: Doc)
    ensures
        r == *d,
{
    match d {
        Doc::Origin(objs) => Doc::Origin(objs.clone()),
        Doc::Schedule(slot) => Doc::Schedule(copy(slot)),
    }
}

/// What a document's view is, variant by variant, for code outside this
/// crate that matches on a `Doc`.
pub proof fn lemma_doc_view(d: &Doc)
    ensures
        d@ == match d {
            Doc::Origin(objs) => DocV::Origin(objs@),
            Doc::Schedule(slot) => DocV::Schedule(*slot),
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
pub open spec fn spec_doc_len(d: DocV) -> nat {
    match d {
        DocV::Origin(m) => m.dom().len(),
        DocV::Schedule(Some(_)) => 1,
        DocV::Schedule(None) => 0,
    }
}

pub fn doc_len(d: &Doc) -> (r: usize)
    ensures
        r as nat == spec_doc_len(d@),
{
    match d {
        Doc::Origin(objs) => {
            proof {
                use_type_invariant(objs);
                lemma_sorted_keys(objs.entries@);
            }
            objs.entries.len()
        },
        Doc::Schedule(Some(_)) => 1,
        Doc::Schedule(None) => 0,
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

/// An origin's empty document.
pub fn empty_origin() -> (r: Doc)
    ensures
        r@ == DocV::Origin(Map::<Seq<char>, ObjV>::empty()),
{
    Doc::Origin(Objects::empty())
}

/// A schedule's empty document.
pub fn empty_schedule() -> (r: Doc)
    ensures
        r@ == DocV::Schedule(None),
{
    Doc::Schedule(None)
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

fn timer(tags: &Tags) -> (r: bool)
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

fn targeted(tags: &Tags) -> (r: bool)
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
fn awaitable(tags: &Tags) -> (r: bool)
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
    {
        proof {
            use_type_invariant(&self);
            lemma_from_entries_sorted(self.entries@);
        }
        self.entries
    }

    /// `spec_due_id` over the keys in order: the first object with something due.
    fn first_due(&self, now: u64) -> (r: Option<String>)
        ensures
            match r {
                Some(id) => spec_due_id(self@, spec_sorted(self@.dom()), now) == Some(id@),
                None => spec_due_id(self@, spec_sorted(self@.dom()), now) is None,
            },
    {
        proof {
            use_type_invariant(self);
            lemma_sorted_keys(self.entries@);
        }
        let ghost map = self@;
        let ghost keys = spec_keys_of(self.entries@);
        let mut i: usize = 0;
        proof {
            assert(keys.skip(0) =~= keys);
        }
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                map == self@,
                keys == spec_keys_of(self.entries@),
                spec_sorted_entries(self.entries@),
                spec_sorted(map.dom()) == keys,
                spec_due_id(map, keys, now) == spec_due_id(map, keys.skip(i as int), now),
            decreases self.entries.len() - i,
        {
            proof {
                lemma_sorted_index(self.entries@, i as int);
                assert(keys.skip(i as int)[0] == self.entries@[i as int].0@);
                assert(keys.skip(i as int).drop_first() =~= keys.skip(i + 1));
            }
            if obj_due(&self.entries[i].1, now).is_some() {
                proof {
                    assert(spec_obj_due(map[keys.skip(i as int)[0]], now) is Some);
                    assert(spec_due_id(map, keys.skip(i as int), now) == Some(keys[i as int]));
                }
                return Some(self.entries[i].0.clone());
            }
            i += 1;
        }
        proof {
            assert(keys.skip(i as int).len() == 0);
        }
        None
    }

    /// `spec_map_deadline` over the keys in order.
    fn deadline(&self) -> (r: Option<u64>)
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
            echod_concrete_spec::model::lemma_string_of(t.pid.unwrap());
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
    let offer = offer_at(&tags, now);
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
            retry_timeout_at: if live { Some(offer) } else { None },
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

/// `spec_empty_doc`.
pub fn empty_doc(key: &String) -> (r: Doc)
    ensures
        r@ == spec_empty_doc(key@),
{
    if is_schedule_key(key) { Doc::Schedule(None) } else { Doc::Origin(Objects::empty()) }
}

/// `spec_is_empty`.
fn is_empty(doc: &Doc) -> (r: bool)
    ensures
        r == spec_is_empty(doc@),
{
    match doc {
        Doc::Origin(objs) => objs.is_empty(),
        Doc::Schedule(slot) => slot.is_none(),
    }
}

/// `spec_origin_map`: the objects of an origin document; none for a schedule.
fn open(doc: Doc) -> (r: Objects)
    ensures
        r@ == spec_origin_map(doc@),
{
    match doc {
        Doc::Origin(objs) => objs,
        Doc::Schedule(_) => Objects::empty(),
    }
}

/// `spec_origin_map(doc)[id]`, copied out, without opening the document.
pub fn peek(doc: &Doc, id: &String) -> (r: Option<Obj>)
    ensures
        match r {
            Some(o) => spec_origin_map(doc@).contains_key(id@) && o@ == spec_origin_map(doc@)[id@],
            None => !spec_origin_map(doc@).contains_key(id@),
        },
{
    match doc {
        Doc::Origin(objs) => objs.get(id),
        Doc::Schedule(_) => None,
    }
}

/// `spec_doc_deadline`.
pub fn doc_deadline(doc: &Doc) -> (r: Option<u64>)
    ensures
        nat_v(r) == spec_doc_deadline(doc@),
{
    match doc {
        Doc::Schedule(Some(schedule)) => Some(schedule.next_run_at),
        Doc::Origin(objs) => objs.deadline(),
        Doc::Schedule(None) => None,
    }
}

/// `spec_earliest_in`.
fn earliest_in(doc: &Doc, now: u64) -> (r: Option<u64>)
    ensures
        r == spec_earliest_in(doc@, now),
{
    match doc {
        Doc::Schedule(Some(schedule)) => if schedule.next_run_at <= now { Some(schedule.next_run_at) } else { None },
        Doc::Origin(objs) => objs.earliest(now),
        Doc::Schedule(None) => None,
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

fn promise_get(doc: Doc, id: &String, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_promise_get(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (Doc::Origin(objs), promise_res(404, None)),
        Some(found) => {
            let obj = project_obj(&found, now);
            let res = promise_res(200, Some(record(id, &obj.promise)));
            (Doc::Origin(objs), res)
        },
    }
}

fn promise_create(doc: Doc, req: &PromiseCreateReq, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_promise_create(doc@, *req, now),
{
    if timer(&req.tags) && targeted(&req.tags) {
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
            (Doc::Origin(objs), res)
        },
    }
}

fn promise_settle(doc: Doc, req: &PromiseSettleReq, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_promise_settle(doc@, *req, now),
{
    if !req.state.settable() {
        return (doc, promise_res(400, None));
    }
    let objs = open(doc);
    match objs.get(&req.id) {
        None => (Doc::Origin(objs), promise_res(404, None)),
        Some(found) => {
            let seen = project_obj(&found, now);
            if !(seen.promise.state == PromiseState::Pending) {
                let res = promise_res(200, Some(record(&req.id, &seen.promise)));
                (Doc::Origin(objs), res)
            } else {
                let obj = settle_obj(seen, req.state, copy(&req.value), now);
                let res = promise_res(200, Some(record(&req.id, &obj.promise)));
                (Doc::Origin(objs.put(&req.id, obj)), res)
            }
        },
    }
}

fn register_callback(doc: Doc, awaited: &String, awaiter: &String, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_register_callback(doc@, *awaited, *awaiter, now),
{
    if *awaited == *awaiter || !same_origin(awaited, awaiter) {
        return (doc, promise_res(400, None));
    }
    let objs = open(doc);
    match objs.get(awaited) {
        None => (Doc::Origin(objs), promise_res(404, None)),
        Some(a) => match objs.get(awaiter) {
            None => (Doc::Origin(objs), promise_res(422, None)),
            Some(b) => {
                let awaited_obj = project_obj(&a, now);
                let awaiter_obj = project_obj(&b, now);
                if !targeted(&awaiter_obj.promise.tags) || !awaitable(&awaited_obj.promise.tags) {
                    (Doc::Origin(objs), promise_res(422, None))
                } else {
                    let res = promise_res(200, Some(record(awaited, &awaited_obj.promise)));
                    if awaited_obj.promise.state == PromiseState::Pending && awaiter_obj.promise.state == PromiseState::Pending {
                        let obj = add_callback(awaited_obj, awaiter);
                        (Doc::Origin(objs.put(awaited, obj)), res)
                    } else {
                        (Doc::Origin(objs), res)
                    }
                }
            },
        },
    }
}

fn register_listener(doc: Doc, awaited: &String, address: &String, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_register_listener(doc@, *awaited, *address, now),
{
    let objs = open(doc);
    match objs.get(awaited) {
        None => (Doc::Origin(objs), promise_res(404, None)),
        Some(found) => {
            let obj = project_obj(&found, now);
            if !awaitable(&obj.promise.tags) {
                (Doc::Origin(objs), promise_res(422, None))
            } else {
                let res = promise_res(200, Some(record(awaited, &obj.promise)));
                if obj.promise.state == PromiseState::Pending {
                    let obj = add_listener(obj, address);
                    (Doc::Origin(objs.put(awaited, obj)), res)
                } else {
                    (Doc::Origin(objs), res)
                }
            }
        },
    }
}

fn task_get(doc: Doc, id: &String, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_task_get(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (Doc::Origin(objs), Response::TaskGet(TaskGetRes { status: 404, task: None })),
        Some(found) => {
            let obj = project_obj(&found, now);
            match &obj.task {
                None => (Doc::Origin(objs), Response::TaskGet(TaskGetRes { status: 404, task: None })),
                Some(t) => {
                    let res = Response::TaskGet(TaskGetRes { status: 200, task: Some(task_record(id, t)) });
                    (Doc::Origin(objs), res)
                },
            }
        },
    }
}

fn task_create(doc: Doc, pid: &String, ttl: u64, action: &PromiseCreateReq, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_task_create(doc@, *pid, ttl, *action, now),
{
    if !targeted(&action.tags) || timer(&action.tags) {
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
                    } else if t.state == TaskState::Pending {
                        let u = acquire(&t, pid, ttl, now);
                        let res = claim_res(200, Some(task_record(&action.id, &u)), Some(record(&action.id, &promise)));
                        let objs = open(doc).put(&action.id, Obj { promise, task: Some(u) });
                        (Doc::Origin(objs), res)
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

fn task_acquire(doc: Doc, id: &String, version: u64, pid: &String, ttl: u64, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_task_acquire(doc@, *id, version, *pid, ttl, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (Doc::Origin(objs), claim_res(404, None, None)),
        Some(found) => {
            let Obj { promise, task } = project_obj(&found, now);
            match task {
                None => (Doc::Origin(objs), claim_res(404, None, None)),
                Some(t) => {
                    if !(t.state == TaskState::Pending) || t.version != version || !(promise.state == PromiseState::Pending) {
                        (Doc::Origin(objs), claim_res(409, None, None))
                    } else {
                        let u = acquire(&t, pid, ttl, now);
                        let res = claim_res(200, Some(task_record(id, &u)), Some(record(id, &promise)));
                        (Doc::Origin(objs.put(id, Obj { promise, task: Some(u) })), res)
                    }
                },
            }
        },
    }
}

fn task_release(doc: Doc, id: &String, version: u64, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_task_release(doc@, *id, version, now),
{
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (Doc::Origin(objs), status_res(404)),
        Lease::Stale => (Doc::Origin(objs), status_res(409)),
        Lease::Ok(obj) => {
            let Obj { promise, task } = obj;
            let task = match task {
                Some(t) => Some(unlease(&t, TaskState::Pending, Some(now))),
                None => None,
            };
            (Doc::Origin(objs.put(id, Obj { promise, task })), status_res(200))
        },
    }
}

fn task_fulfill(doc: Doc, id: &String, version: u64, action: &PromiseSettleReq, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_task_fulfill(doc@, *id, version, *action, now),
{
    if !action.state.settable() {
        return (doc, promise_res(400, None));
    }
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (Doc::Origin(objs), promise_res(404, None)),
        Lease::Stale => (Doc::Origin(objs), promise_res(409, None)),
        Lease::Ok(obj) => {
            let obj = settle_obj(obj, action.state, copy(&action.value), now);
            let res = promise_res(200, Some(record(id, &obj.promise)));
            (Doc::Origin(objs.put(id, obj)), res)
        },
    }
}

fn task_halt(doc: Doc, id: &String, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_task_halt(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (Doc::Origin(objs), status_res(404)),
        Some(found) => {
            let Obj { promise, task } = project_obj(&found, now);
            match task {
                None => (Doc::Origin(objs), status_res(404)),
                Some(t) => {
                    if t.state == TaskState::Fulfilled {
                        (Doc::Origin(objs), status_res(409))
                    } else if t.state == TaskState::Halted {
                        (Doc::Origin(objs), status_res(200))
                    } else {
                        let obj = Obj { promise, task: Some(unlease(&t, TaskState::Halted, None)) };
                        (Doc::Origin(objs.put(id, obj)), status_res(200))
                    }
                },
            }
        },
    }
}

fn task_continue(doc: Doc, id: &String, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_task_continue(doc@, *id, now),
{
    let objs = open(doc);
    match objs.get(id) {
        None => (Doc::Origin(objs), status_res(404)),
        Some(found) => {
            let Obj { promise, task } = project_obj(&found, now);
            match task {
                None => (Doc::Origin(objs), status_res(404)),
                Some(t) => {
                    if !(t.state == TaskState::Halted) || !(promise.state == PromiseState::Pending) {
                        (Doc::Origin(objs), status_res(409))
                    } else {
                        let mut u = t;
                        u.state = TaskState::Pending;
                        u.retry_timeout_at = Some(now);
                        (Doc::Origin(objs.put(id, Obj { promise, task: Some(u) })), status_res(200))
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

fn heartbeat(doc: Doc, pid: &String, tasks: &Vec<TaskRef>, now: u64) -> (r: (Doc, Response))
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
    (Doc::Origin(objs), status_res(200))
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

fn suspend(doc: Doc, id: &String, version: u64, actions: &Vec<PromiseRegisterCallbackReq>, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_suspend(doc@, *id, version, actions@, now),
{
    if actions.len() == 0 || bad_suspend(actions, id) || !distinct_awaited(actions) {
        return (doc, status_res(400));
    }
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (Doc::Origin(objs), status_res(404)),
        Lease::Stale => (Doc::Origin(objs), status_res(409)),
        Lease::Ok(obj) => {
            if missing_awaited(&objs, actions) || unawaitable(&objs, actions) {
                (Doc::Origin(objs), status_res(422))
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
                (Doc::Origin(objs.put(id, Obj { promise, task })), status_res(300))
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
                        (Doc::Origin(objs.put(id, Obj { promise, task })), status_res(200))
                    },
                    None => {
                        proof {
                            assert(false);
                        }
                        (Doc::Origin(objs), status_res(500))
                    },
                }
            }
        },
    }
}

fn fence(doc: Doc, id: &String, version: u64, action: &TaskFenceAction, now: u64) -> (r: (Doc, Response))
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
        Lease::Missing => (Doc::Origin(objs), fence_res(404, None)),
        Lease::Stale => (Doc::Origin(objs), fence_res(409, None)),
        Lease::Ok(_) => {
            let doc = Doc::Origin(objs);
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

fn fence_check(doc: Doc, id: &String, version: u64, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_fence_check(doc@, *id, version, now),
{
    let objs = open(doc);
    match held(&objs, id, version, now) {
        Lease::Missing => (Doc::Origin(objs), status_res(404)),
        Lease::Stale => (Doc::Origin(objs), status_res(409)),
        Lease::Ok(_) => (Doc::Origin(objs), status_res(200)),
    }
}

fn schedule_get(doc: Doc, id: &String) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_schedule_get(doc@, *id),
{
    let found = match &doc {
        Doc::Schedule(Some(schedule)) => {
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

fn schedule_create(doc: Doc, req: &ScheduleCreateReq, now: u64) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_schedule_create(doc@, *req, now),
{
    if targeted(&req.promise_tags) && timer(&req.promise_tags) {
        return (doc, Response::Schedule(ScheduleRes { status: 400, schedule: None }));
    }
    let existing = match &doc {
        Doc::Schedule(Some(schedule)) => Some(copy(schedule)),
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
                next_run_at: next_cron(&req.cron, now),
                last_run_at: None,
                created_at: now,
            };
            let answer = copy(&schedule);
            (Doc::Schedule(Some(schedule)), Response::Schedule(ScheduleRes { status: 200, schedule: Some(answer) }))
        },
    }
}

fn schedule_delete(doc: Doc, id: &String) -> (r: (Doc, Response))
    ensures
        (r.0@, r.1) == spec_schedule_delete(doc@, *id),
{
    let matched = match &doc {
        Doc::Schedule(Some(schedule)) => {
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
        (Doc::Schedule(None), status_res(200))
    } else {
        (doc, status_res(404))
    }
}

/// `spec_handle`: the same match.
pub fn handle(doc: Doc, request: &Request, now: u64) -> (r: (Doc, Response))
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

/// `spec_resume`: a suspended awaiter is offered again from `since`.
fn resume(objs: Objects, awaiter: &String, awaited: &String, since: u64, now: u64) -> (r: Objects)
    ensures
        r@ == spec_resume(objs@, awaiter@, awaited@, since, now),
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
                            retry_timeout_at: Some(since),
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

/// `spec_step_object`: one object's due work.
fn step_object(objs: Objects, id: &String, now: u64, retry_timeout: u64) -> (r: (Objects, Vec<Outbound>))
    ensures
        spec_step_object(objs@, id@, now, retry_timeout) == (r.0@, notes_v(r.1@)),
{
    proof {
        lemma_notes_empty();
    }
    match objs.get(id) {
        None => (objs, Vec::new()),
        Some(obj) => {
            if obj.promise.state == PromiseState::Pending && obj.promise.timeout_at <= now {
                let projected = project_obj(&obj, now);
                (objs.put(id, projected), Vec::new())
            } else if obj.promise.state == PromiseState::Pending {
                let Obj { promise, task } = obj;
                match task {
                    Some(t) => {
                        let lease_over = t.state == TaskState::Acquired
                            && match t.lease_timeout_at { Some(at) => at <= now, None => false };
                        let retry_over = t.state == TaskState::Pending
                            && match t.retry_timeout_at { Some(at) => at <= now, None => false };
                        if lease_over {
                            let u = unlease(&t, TaskState::Pending, Some(now));
                            (objs.put(id, Obj { promise, task: Some(u) }), Vec::new())
                        } else if retry_over {
                            let version = t.version;
                            let mut u = t;
                            u.retry_timeout_at = Some(sat_add(now, retry_timeout));
                            let mut notes: Vec<Outbound> = Vec::new();
                            let note = Outbound::Execute { id: id.clone(), version };
                            proof {
                                lemma_notes_one(note);
                            }
                            notes.push(note);
                            (objs.put(id, Obj { promise, task: Some(u) }), notes)
                        } else {
                            (objs, Vec::new())
                        }
                    },
                    None => (objs, Vec::new()),
                }
            } else if obj.promise.callbacks.len() > 0 {
                let Obj { promise, task } = obj;
                let mut promise = promise;
                let ghost before = promise.callbacks@;
                let awaiter = promise.callbacks.remove(0);
                proof {
                    lemma_strs_skip(before);
                }
                let since = match promise.settled_at { Some(t) => t, None => 0 };
                let objs = objs.put(id, Obj { promise, task });
                (resume(objs, &awaiter, id, since, now), Vec::new())
            } else if obj.promise.listeners.len() > 0 {
                let Obj { promise, task } = obj;
                let mut promise = promise;
                let ghost before = promise.listeners@;
                let address = promise.listeners.remove(0);
                proof {
                    lemma_strs_skip(before);
                    echod_concrete_spec::model::lemma_string_of(*id);
                }
                let rec = record(id, &promise);
                let mut notes: Vec<Outbound> = Vec::new();
                let note = Outbound::Unblock { address, promise: rec };
                proof {
                    lemma_notes_one(note);
                }
                notes.push(note);
                (objs.put(id, Obj { promise, task }), notes)
            } else {
                (objs, Vec::new())
            }
        },
    }
}

/// `spec_run_due`: a schedule fires, or the first due object steps.
pub fn run_due(doc: Doc, now: u64, retry_timeout: u64) -> (r: (Doc, Vec<Pending>, Vec<Outbound>))
    ensures
        spec_run_due(doc@, now, retry_timeout) == (r.0@, None::<Response>, pend_v(r.1@), notes_v(r.2@)),
{
    proof {
        lemma_notes_empty();
        lemma_pend_empty();
    }
    match doc {
        Doc::Schedule(Some(schedule)) => {
            if schedule.next_run_at <= now {
                let at = schedule.next_run_at;
                let pending = Pending {
                    promise: expand(&schedule.promise_id, &schedule.id, at),
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
                let mut born: Vec<Pending> = Vec::new();
                born.push(pending);
                (Doc::Schedule(Some(next)), born, Vec::new())
            } else {
                (Doc::Schedule(Some(schedule)), Vec::new(), Vec::new())
            }
        },
        Doc::Origin(objs) => {
            match objs.first_due(now) {
                Some(id) => {
                    let (objs, notes) = step_object(objs, &id, now, retry_timeout);
                    (Doc::Origin(objs), Vec::new(), notes)
                },
                None => (Doc::Origin(objs), Vec::new(), Vec::new()),
            }
        },
        Doc::Schedule(None) => (Doc::Schedule(None), Vec::new(), Vec::new()),
    }
}

/// `spec_occurrence`: the promise a schedule occurrence creates, once it is due.
pub fn create_occurrence(doc: Doc, pending: &Pending, now: u64) -> (r: Doc)
    ensures
        r@ == spec_occurrence(doc@, pending@, now),
{
    let objs = open(doc);
    if objs.contains(&pending.promise) || now < pending.at {
        return Doc::Origin(objs);
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
                u.retry_timeout_at = Some(offer_at(&pending.tags, pending.at));
                Some(u)
            } else {
                Some(t)
            }
        },
        None => None,
    };
    Doc::Origin(objs.put(&pending.promise, Obj { promise, task }))
}

/// `spec_sweep`: `run_due` again and again, until a step leaves the document
/// as it was or `limit` steps have run. What the steps queue and tell, in order.
pub fn sweep(from: Doc, now: u64, retry_timeout: u64, limit: u64) -> (r: (Doc, Vec<Pending>, Vec<Outbound>))
    ensures
        (r.0@, pend_v(r.1@), notes_v(r.2@)) == spec_sweep(from@, now, retry_timeout, limit as nat),
{
    let ghost start = from@;
    let mut doc = from;
    let mut born: Vec<Pending> = Vec::new();
    let mut notes: Vec<Outbound> = Vec::new();
    let mut left: u64 = limit;
    proof {
        lemma_pend_empty();
        lemma_notes_empty();
        assert(Seq::<PendingV>::empty() + spec_sweep(doc@, now, retry_timeout, left as nat).1 =~= spec_sweep(doc@, now, retry_timeout, left as nat).1);
        assert(Seq::<NoteV>::empty() + spec_sweep(doc@, now, retry_timeout, left as nat).2 =~= spec_sweep(doc@, now, retry_timeout, left as nat).2);
    }
    while left > 0
        invariant
            start == from@,
            ({
                let (d, p, n) = spec_sweep(doc@, now, retry_timeout, left as nat);
                spec_sweep(start, now, retry_timeout, limit as nat) == (d, pend_v(born@) + p, notes_v(notes@) + n)
            }),
        decreases left,
    {
        let (next, mut p, mut n) = run_due(copy(&doc), now, retry_timeout);
        if same_doc(&next, &doc) {
            proof {
                assert(spec_run_due(doc@, now, retry_timeout).0 == doc@);
                assert(left as nat != 0);
                assert(spec_sweep(doc@, now, retry_timeout, left as nat) == (doc@, Seq::<PendingV>::empty(), Seq::<NoteV>::empty()));
                assert(pend_v(born@) + Seq::<PendingV>::empty() =~= pend_v(born@));
                assert(notes_v(notes@) + Seq::<NoteV>::empty() =~= notes_v(notes@));
            }
            return (doc, born, notes);
        }
        let ghost (p0, n0) = (p@, n@);
        let ghost (b0, s0) = (born@, notes@);
        born.append(&mut p);
        notes.append(&mut n);
        proof {
            lemma_map_values_add(b0, p0);
            lemma_notes_add(s0, n0);
            let (d, pp, nn) = spec_sweep(next@, now, retry_timeout, (left - 1) as nat);
            assert(pend_v(b0) + (pend_v(p0) + pp) =~= (pend_v(b0) + pend_v(p0)) + pp);
            assert(notes_v(s0) + (notes_v(n0) + nn) =~= (notes_v(s0) + notes_v(n0)) + nn);
        }
        doc = next;
        left = left - 1;
    }
    proof {
        assert(pend_v(born@) + Seq::<PendingV>::empty() =~= pend_v(born@));
        assert(notes_v(notes@) + Seq::<NoteV>::empty() =~= notes_v(notes@));
    }
    (doc, born, notes)
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
// The codec. Verus reads it through `spec_encode` and `spec_read`: what
// `encode` wrote, `decode` reads back, and a body that does not parse is
// the empty document for the key.
// ---------------------------------------------------------------------------

#[cfg(not(verus_keep_ghost))]
fn encode(doc: &Doc) -> Vec<u8> {
    serde_json::to_vec(doc).unwrap_or_default()
}

#[cfg(not(verus_keep_ghost))]
fn decode(key: &String, body: &Vec<u8>) -> Doc {
    match serde_json::from_slice::<Doc>(body) {
        Ok(Doc::Origin(objs)) => Doc::Origin(objs.in_order()),
        Ok(doc) => doc,
        Err(_) => empty_doc(key),
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
fn encode(_doc: &Doc) -> Vec<u8> {
    Vec::new()
}

#[cfg(verus_keep_ghost)]
fn decode(key: &String, _body: &Vec<u8>) -> Doc {
    empty_doc(key)
}

verus! {

pub assume_specification [encode](doc: &Doc) -> (r: Vec<u8>)
    ensures
        r@ == spec_encode(doc@);

pub assume_specification [decode](key: &String, body: &Vec<u8>) -> (r: Doc)
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
        echod_concrete_spec::model::lemma_string_of(*client);
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
                echod_concrete_spec::model::lemma_string_of(*id);
            }
            (Pid::Outside, Message::Output(Output::Dispatch(Dispatch::Execute { id: id.clone(), version: *version })))
        },
        Outbound::Unblock { address, promise } => {
            proof {
                echod_concrete_spec::model::lemma_string_of(*address);
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
fn remember_in(cache: &mut Vec<Cached>, key: &String, doc: Doc, etag: Option<Etag>)
    ensures
        docs_v(final(cache)@) == spec_remember(docs_v(old(cache)@), key@, spec_encode(doc@), etag_v(etag), 0),
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
fn keep_in(cache: &mut Vec<Cached>, key: &String, doc: Doc, etag: Option<Etag>)
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
    fn cached(&self, key: &String) -> (r: Option<(Doc, Option<Etag>)>)
        ensures
            match r {
                Some((doc, etag)) => spec_cached(self@, key@) == Some(CachedV { key: key@, body: spec_encode(doc@), etag: etag_v(etag) }),
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
                    axiom_decode_encode(doc@);
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
                    echod_concrete_spec::model::lemma_string_of(key);
                }
                (next, one((Pid::Store, Message::StoreReq { op, call: StoreCall::Get { key } })))
            },
        }
    }

    /// `spec_decide`: run the job; answer at once when the document stands, else write it back.
    fn decide(self, flight: Flight, doc: Doc) -> (r: (Node, Vec<(Pid, Message)>))
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
        let (next, answer, born, notify): (Doc, Option<Response>, Vec<Pending>, Vec<Outbound>) = match &job {
            Job::External { request } => {
                let (next, response) = handle(doc, request, now);
                (next, Some(response), Vec::new(), Vec::new())
            },
            Job::Due => {
                let (next, born, notify) = run_due(doc, now, self.retry_timeout);
                (next, None, born, notify)
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
        let previous: Doc = match self.cached(&key) {
            Some((d, _)) => {
                proof {
                    axiom_decode_encode(d@);
                }
                d
            },
            None => empty_doc(&key),
        };
        if same_doc(&next, &previous) && born.len() == 0 {
            let mut node = self;
            node.flight = None;
            keep_in(&mut node.cache, &key, next, etag);
            let send = sent(&reply_slot, &notify);
            (node, send)
        } else {
            let op = self.next_op;
            let body = encode(&next);
            proof {
                echod_concrete_spec::model::lemma_bytes_realised(spec_encode(next@));
                axiom_vec_ext(body, spec_bytes(spec_encode(next@)));
                echod_concrete_spec::model::lemma_string_of(key);
            }
            let call = match &etag {
                Some(tag) => {
                    proof {
                        echod_concrete_spec::model::lemma_string_of(tag.0);
                    }
                    StoreCall::PutIfMatch { key: key.clone(), body, etag: copy(tag) }
                },
                None => StoreCall::PutIfNoneMatch { key: key.clone(), body },
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
            (node, one((Pid::Store, Message::StoreReq { op, call })))
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
    fn store_reply(self, op: u64, outcome: &StoreOutcome) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.next_op < u64::MAX,
        ensures
            (r.0@, r.1@) == spec_store_reply(self@, op, *outcome),
    {
        match &self.flight {
            None => (self, Vec::new()),
            Some(f) => {
                let flight = copy(f);
                if flight.op != op {
                    return (self, Vec::new());
                }
                if !flight.writing {
                    match outcome {
                        StoreOutcome::Got(got) => {
                            let (doc, etag): (Doc, Option<Etag>) = match got {
                                Some(pair) => (decode(&flight.key, &pair.0), Some(copy(&pair.1))),
                                None => (empty_doc(&flight.key), None),
                            };
                            let mut flight = flight;
                            flight.etag = etag;
                            let mut node = self;
                            node.flight = None;
                            node.decide(flight, doc)
                        },
                        StoreOutcome::Failed(_) => {
                            let mut node = self;
                            node.flight = None;
                            node.fail(flight)
                        },
                        _ => (self, Vec::new()),
                    }
                } else {
                    match outcome {
                        StoreOutcome::Written(tag) => self.commit(flight, copy(tag)),
                        StoreOutcome::Failed(_) => {
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
            if !node.owns(&key) {
                return (node, Vec::new());
            }
            return node.begin(key, Job::Occurrence(pending), now, None);
        }
        match self.earliest_due(now) {
            Some(key) => self.begin(key, Job::Due, now, None),
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
                axiom_decode_encode(self.cache@[i as int].doc@);
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
                axiom_decode_encode(self.cache@[i as int].doc@);
            }
            let entry = &self.cache[i];
            if self.owns(&entry.key) {
                acc = min_u64(doc_deadline(&entry.doc), acc);
            }
        }
        let from_pending = if self.pending.len() == 0 { None } else { Some(self.pending[0].at) };
        min_u64(from_pending, acc)
    }

    /// A node of the fleet, before its first event: `spec_initial_node`.
    pub fn new(address: u64, nodes: u64, loops: bool, retry_timeout: u64) -> (r: Node)
        ensures
            r@ == spec_initial_node(Config { nodes, loops, appendable: false, retry_timeout }, address),
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
    fn after_store_reply(&self, now: u64, op: u64, outcome: &StoreOutcome) -> (r: (Node, Vec<(Pid, Message)>))
        requires
            self.flight is Some,
            self.next_op < u64::MAX,
        ensures
            ({
                let (next, send) = spec_store_reply(self@, op, *outcome);
                r.0@ == (NodeV { logic: spec_clock(self@.logic, now), wake: spec_wake(next), ..next })
                && r.1@ == send
            }),
    {
        let (next, send) = copy(self).store_reply(op, outcome);
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
            ProcessEvent::Receive { sender: Pid::Store, message: Message::StoreReply { op, outcome } } => {
                if self.flight.is_none() || self.next_op == u64::MAX {
                    results_one(copy(self), Vec::new())
                } else {
                    let (next, send) = self.after_store_reply(now, *op, outcome);
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
pub open spec fn node_results_v(pairs: Seq<(Node, Vec<(Pid, Message)>)>) -> Seq<StepResultV<Proc, Pid, Message>> {
    pairs.map_values(|pair: (Node, Vec<(Pid, Message)>)| StepResultV { state: Proc::Node(pair.0@), send: pair.1@ })
}

proof fn lemma_results_empty()
    ensures
        node_results_v(Seq::<(Node, Vec<(Pid, Message)>)>::empty()) == Seq::<StepResultV<Proc, Pid, Message>>::empty(),
{
    assert(node_results_v(Seq::<(Node, Vec<(Pid, Message)>)>::empty()) =~= Seq::<StepResultV<Proc, Pid, Message>>::empty());
}

/// `spec_one`: the one result of a step.
fn results_one(node: Node, send: Vec<(Pid, Message)>) -> (r: Vec<(Node, Vec<(Pid, Message)>)>)
    ensures
        node_results_v(r@) == spec_one(Proc::Node(node@), send@),
{
    let ghost nv = node@;
    let ghost sv = send@;
    let mut r: Vec<(Node, Vec<(Pid, Message)>)> = Vec::new();
    r.push((node, send));
    proof {
        assert(node_results_v(r@) =~= spec_one(Proc::Node(nv), sv));
    }
    r
}

} // verus!
