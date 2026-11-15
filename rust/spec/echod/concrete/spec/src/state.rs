//! state definitions for the concrete model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::rover::{Pid};
use rover_spec::rover::comm::Time;

verus! {
#[cfg(verus_keep_ghost)]
pub enum ChangeV<V> {
    Upsert { id: Seq<char>, value: V },
    Remove { id: Seq<char> },
}

#[cfg(verus_keep_ghost)]
pub struct PartialV<V> {
    pub document: Seq<char>,
    pub basever: nat,
    pub version: nat,
    pub committed_at: nat,
    pub next_wake_at: Option<nat>,
    pub changes: Seq<ChangeV<V>>,
}

#[cfg(verus_keep_ghost)]
pub struct FoldedV<V> {
    pub document: Seq<char>,
    pub version: nat,
    pub committed_at: nat,
    pub next_wake_at: Option<nat>,
    pub entries: Map<Seq<char>, V>,
}

pub struct PromV {
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
    pub callbacks: Seq<Seq<char>>,
    pub listeners: Seq<Seq<char>>,
}

pub struct TkV {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<Seq<char>>,
    pub ttl: Option<u64>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Seq<Seq<char>>,
}

pub struct ObjV {
    pub promise: PromV,
    pub task: Option<TkV>,
}

pub struct PromiseEffectV {
    pub id: Seq<char>,
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
}

pub enum ProtocolEffectV {
    Execute { id: Seq<char>, version: u64 },
    Unblock {
        promise: Seq<char>,
        address: Seq<char>,
        record: PromiseEffectV,
    },
}

pub enum ProtocolEffectKeyV {
    Execute { id: Seq<char> },
    Unblock { promise: Seq<char>, address: Seq<char> },
}

pub enum TimerEffectV {
    Add { at: u64 },
    Delete { at: u64 },
}

pub enum DocumentBodyV {
    Workflow(Map<Seq<char>, ObjV>),
    Schedule(Option<Schedule>),
}

pub struct WorkflowDocumentV {
    pub document: Seq<char>,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub objects: Map<Seq<char>, ObjV>,
}

pub struct ScheduleDocumentV {
    pub document: Seq<char>,
    pub version: u64,
    pub committed_at: u64,
    pub next_wake_at: Option<u64>,
    pub schedule: Option<Schedule>,
}

pub enum StoredDocumentV {
    Workflow(WorkflowDocumentV),
    Schedule(ScheduleDocumentV),
}

pub struct LoadedDocumentV {
    pub document: StoredDocumentV,
    pub change_count: usize,
    pub bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Message {
    Request(Call),
    Output(Output),
    StoreReq { op: u64, request: StoreReq },
    StoreRes { op: u64, response: StoreRes },
    Stop,
}

pub struct LogicV {
    pub clock: nat,
    pub loops: bool,
    pub stopping: bool,
    pub stopped: bool,
    pub last_wake: Option<nat>,
}

pub enum Proc {
    Node(NodeV),
    Store(StoreV),
}

pub const REQUEST_SWEEP_STEPS: u64 = u64::MAX;

pub struct PendingV {
    pub promise: Seq<char>,
    pub at: u64,
    pub timeout: u64,
    pub param: Value,
    pub tags: Tags,
}

pub enum NoteV {
    Execute { id: Seq<char>, version: u64 },
    Unblock { address: Seq<char>, promise: PromiseRecord },
}

pub enum NoteKeyV {
    Execute(Seq<char>),
    Unblock(Seq<char>, Seq<char>),
}

pub enum JobV {
    External(Request),
    Due,
    Occurrence(PendingV),
}

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

pub struct CachedV {
    pub key: Seq<char>,
    pub body: Seq<u8>,
    pub etag: Option<Seq<char>>,
}

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

pub enum Held { Ok(ObjV), Missing, Stale }

#[make_spec_type]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Etag(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreError {
    /// A conditional write found the object at another version.
    PreconditionFailed,
    /// The store did not answer, or answered with an error: the effect of
    /// a write is unknown.
    Unavailable(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Read {
    Body(Vec<u8>, Etag),
    NotModified,
    Absent,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreReq {
    Get { key: String },
    GetIfNoneMatch { key: String, etag: Etag },
    PutIfMatch { key: String, body: Vec<u8>, etag: Etag },
    PutIfNoneMatch { key: String, body: Vec<u8> },
    AppIfMatch { key: String, offset: u64, body: Vec<u8>, etag: Etag },
    Put { key: String, body: Vec<u8> },
    Del { key: String },
    List { prefix: String, max_keys: usize },
    ListPrefixes { prefix: String },
}

#[allow(inconsistent_fields)]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum StoreRes {
    Get { result: Result<Option<(Vec<u8>, Etag)>, StoreError> },
    GetIfNoneMatch { result: Result<Read, StoreError> },
    PutIfMatch { result: Result<Etag, StoreError> },
    PutIfNoneMatch { result: Result<Etag, StoreError> },
    AppIfMatch { result: Result<Etag, StoreError> },
    Put { result: Result<(), StoreError> },
    Del { result: Result<(), StoreError> },
    List { result: Result<Vec<String>, StoreError> },
    ListPrefixes { result: Result<Vec<String>, StoreError> },
}

pub ghost enum StoreErrorSpec {
    PreconditionFailed,
    Unavailable(Seq<char>),
}

impl DeepView for StoreError {
    type V = StoreErrorSpec;
    open spec fn deep_view(&self) -> StoreErrorSpec {
        match self {
            StoreError::PreconditionFailed => StoreErrorSpec::PreconditionFailed,
            StoreError::Unavailable(m) => StoreErrorSpec::Unavailable(m@),
        }
    }
}

#[cfg(verus_keep_ghost)]
pub ghost enum ReadSpec {
    Body(Seq<u8>, EtagSpec),
    NotModified,
    Absent,
}

#[cfg(verus_keep_ghost)]
impl DeepView for Read {
    type V = ReadSpec;
    open spec fn deep_view(&self) -> ReadSpec {
        match self {
            Read::Body(b, e) => ReadSpec::Body(b@, e.deep_view()),
            Read::NotModified => ReadSpec::NotModified,
            Read::Absent => ReadSpec::Absent,
        }
    }
}

#[cfg(verus_keep_ghost)]
pub ghost enum StoreReqSpec {
    Get { key: Seq<char> },
    GetIfNoneMatch { key: Seq<char>, etag: EtagSpec },
    PutIfMatch { key: Seq<char>, body: Seq<u8>, etag: EtagSpec },
    PutIfNoneMatch { key: Seq<char>, body: Seq<u8> },
    AppIfMatch { key: Seq<char>, offset: u64, body: Seq<u8>, etag: EtagSpec },
    Put { key: Seq<char>, body: Seq<u8> },
    Del { key: Seq<char> },
    List { prefix: Seq<char>, max_keys: usize },
    ListPrefixes { prefix: Seq<char> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for StoreReq {
    type V = StoreReqSpec;
    open spec fn deep_view(&self) -> StoreReqSpec {
        match self {
            StoreReq::Get { key } => StoreReqSpec::Get { key: key@ },
            StoreReq::GetIfNoneMatch { key, etag } => StoreReqSpec::GetIfNoneMatch { key: key@, etag: etag.deep_view() },
            StoreReq::PutIfMatch { key, body, etag } => StoreReqSpec::PutIfMatch { key: key@, body: body@, etag: etag.deep_view() },
            StoreReq::PutIfNoneMatch { key, body } => StoreReqSpec::PutIfNoneMatch { key: key@, body: body@ },
            StoreReq::AppIfMatch { key, offset, body, etag } => StoreReqSpec::AppIfMatch { key: key@, offset: *offset, body: body@, etag: etag.deep_view() },
            StoreReq::Put { key, body } => StoreReqSpec::Put { key: key@, body: body@ },
            StoreReq::Del { key } => StoreReqSpec::Del { key: key@ },
            StoreReq::List { prefix, max_keys } => StoreReqSpec::List { prefix: prefix@, max_keys: *max_keys },
            StoreReq::ListPrefixes { prefix } => StoreReqSpec::ListPrefixes { prefix: prefix@ },
        }
    }
}

impl DeepView for StoreRes {
    type V = StoreRes;
    open spec fn deep_view(&self) -> StoreRes {
        *self
    }
}

pub struct EntryV {
    pub key: Seq<char>,
    pub body: Seq<u8>,
    pub version: nat,
}

pub struct StoreV {
    pub entries: Seq<EntryV>,
    pub appendable: bool,
    /// The `(node, op)` pairs the store has answered. A second delivery of
    /// one is a stutter.
    pub seen: Seq<(Pid, u64)>,
}

#[cfg(not(verus_keep_ghost))]
impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoreError::PreconditionFailed => f.write_str("precondition failed"),
            StoreError::Unavailable(m) => write!(f, "store unavailable: {m}"),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl std::error::Error for StoreError {

}
}
