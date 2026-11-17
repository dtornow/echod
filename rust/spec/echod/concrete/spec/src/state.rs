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
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionConfigData {
    pub node_id: String,
    pub url: String,
    pub prefix: String,
    pub compact: u32,
    pub appendable: bool,
    pub retry_timeout: u64,
    pub timer_bucket_ms: u64,
    pub heartbeat_ms: u64,
    pub node_ttl_ms: u64,
    pub cache_entries: usize,
    pub cache_bytes: u64,
    pub debug: bool,
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionConfigData {
    type V = ProductionConfigV;
    open spec fn deep_view(&self) -> Self::V {
        ProductionConfigV {
            node_id: self.node_id@, url: self.url@, prefix: self.prefix@, compact: self.compact,
            appendable: self.appendable, retry_timeout: self.retry_timeout, timer_bucket_ms: self.timer_bucket_ms,
            heartbeat_ms: self.heartbeat_ms, node_ttl_ms: self.node_ttl_ms, cache_entries: self.cache_entries,
            cache_bytes: self.cache_bytes, debug: self.debug,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionModelConfig {
    pub node: ProductionConfigData,
    pub loops: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionFleetConfig {
    pub nodes: Vec<ProductionConfigData>,
    pub loops: bool,
    pub appendable: bool,
    pub fault: Option<String>,
}

pub struct ProductionRoutedNodeV {
    pub node: ProductionNodeModel,
    pub id: u64,
    pub wake: Option<(u64, ProductionArmed)>,
    pub next_request: u64,
    pub pending: Seq<ProductionPublicRoute>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionPublicCall {
    pub client: String,
    pub id: u64,
    pub kind: String,
    pub corr: String,
    pub request: Request,
    pub action_kind: Option<String>,
    pub now: u64,
    pub pinned: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionPublicRoute {
    pub internal: u64,
    pub call: ProductionPublicCall,
}

pub enum ProductionFleetModel {
    Node(ProductionRoutedNodeV),
    Store(StoreV),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionWireMessage {
    Input(ProductionInput),
    Effect(ProductionEffectData),
    StoreCall { op: u64, request: StoreReq },
    StoreReply { op: u64, response: StoreRes },
    PublicRequest(ProductionPublicCall),
    PublicResult { call: ProductionPublicCall, response: Result<ProductionAnswerData, String> },
}

pub struct ProductionNodeModel {
    #[cfg(verus_keep_ghost)]
    pub core: ProductionStateV,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionPromiseData {
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

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionPromiseData {
    type V = PromV;
    open spec fn deep_view(&self) -> Self::V {
        PromV {
            state: self.state, param: self.param, value: self.value, tags: self.tags,
            timeout_at: self.timeout_at, created_at: self.created_at, settled_at: self.settled_at,
            callbacks: self.callbacks.deep_view(), listeners: self.listeners.deep_view(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionTaskData {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<String>,
    pub ttl: Option<u64>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Vec<String>,
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionTaskData {
    type V = TkV;
    open spec fn deep_view(&self) -> Self::V {
        TkV {
            state: self.state, version: self.version, pid: self.pid.deep_view(), ttl: self.ttl,
            lease_timeout_at: self.lease_timeout_at, retry_timeout_at: self.retry_timeout_at,
            resumes: self.resumes.deep_view(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionObjectData {
    pub promise: ProductionPromiseData,
    pub task: Option<ProductionTaskData>,
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionObjectData {
    type V = ObjV;
    open spec fn deep_view(&self) -> Self::V {
        ObjV { promise: self.promise.deep_view(), task: self.task.deep_view() }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionDocumentData {
    Workflow(Vec<(String, ProductionObjectData)>),
    Schedule(Option<Schedule>),
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionDocumentData {
    type V = DocumentBodyV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Workflow(entries) => DocumentBodyV::Workflow(crate::handler::production_document_data_rows(entries.deep_view())),
            Self::Schedule(schedule) => DocumentBodyV::Schedule(*schedule),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionDebugData {
    Object,
    List,
    Message(String),
    Snap { origins: Vec<ProductionDocumentData>, schedules: Vec<Schedule> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionDebugData {
    type V = ProductionDebugBodyV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Object => ProductionDebugBodyV::Object,
            Self::List => ProductionDebugBodyV::List,
            Self::Message(message) => ProductionDebugBodyV::Message(message@),
            Self::Snap { origins, schedules } => ProductionDebugBodyV::Snap {
                origins: origins.deep_view(), schedules: schedules.deep_view(),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionAnswerData {
    Step { kind: String, corr: String, action_kind: Option<String>, response: Response, why: Option<String> },
    Debug { kind: String, corr: String, status: u16, body: ProductionDebugData },
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionAnswerData {
    type V = ProductionAnswerV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Step { kind, corr, action_kind, response, why } => ProductionAnswerV::Step {
                kind: kind@, corr: corr@, action_kind: action_kind.deep_view(), response: response.deep_view(), why: why.deep_view(),
            },
            Self::Debug { kind, corr, status, body } => ProductionAnswerV::Debug {
                kind: kind@, corr: corr@, status: *status, body: body.deep_view(),
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionDispatchData {
    Execute { task_id: String, version: u64 },
    Unblock(PromiseRecord),
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionDispatchData {
    type V = ProductionMessageV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Execute { task_id, version } => ProductionMessageV::Execute { task_id: task_id@, version: *version },
            Self::Unblock(promise) => ProductionMessageV::Unblock(promise.deep_view()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionEffectData {
    Reply { id: u64, response: Result<ProductionAnswerData, String> },
    Store { op: u64, request: StoreReq },
    Wake { after_ms: u64, armed: ProductionArmed },
    Send { address: String, message: ProductionDispatchData },
    Note(ProductionNoteData),
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionEffectData {
    type V = ProductionEffectV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Reply { id, response } => ProductionEffectV::Reply { id: *id, response: response.deep_view() },
            Self::Store { op, request } => ProductionEffectV::Store { op: *op, request: request.deep_view() },
            Self::Wake { after_ms, armed } => ProductionEffectV::Wake { after_ms: *after_ms, armed: *armed },
            Self::Send { address, message } => ProductionEffectV::Send { address: address@, message: message.deep_view() },
            Self::Note(note) => ProductionEffectV::Note(note.deep_view()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionNoteData {
    DocumentWrite { mode: ProductionWriteMode, bytes: usize },
    Commit(ProductionCommitOutcome),
    Cache(ProductionCacheResult),
    MembershipRefresh { ok: bool },
    ConfigurationChange,
    ConfigurationWrite(ProductionConfigWrite),
    TimerFire { kind: ProductionTimerKind, outcome: ProductionFireOutcome, lag_ms: u64 },
    TimerListing { ok: bool },
    Sweep(ProductionSweepOutcome),
    SweepBegin { flight: u64, target: String, now: u64 },
    SweepEnd { flight: u64, committed: bool },
    FireBegin { flight: u64, origin: String, now: u64, row: Box<Schedule>, at: u64, promise_id: String, next: u64 },
    FireEnd { flight: u64, committed: bool },
    AdvanceBegin { flight: u64, schedule: String, now: u64, at: u64, next: u64 },
    AdvanceEnd { flight: u64, committed: bool },
    ConfigurationRead { epoch: u64, members: Vec<String> },
    ConfigurationWritten { epoch: u64, members: Vec<String> },
    TimersLoaded { deadlines: usize, wheel: usize, epoch: u64 },
    BucketLoaded { bucket: u64, deadlines: usize },
    Raced { target: String, attempt: u32 },
    KeyNotDeleted { key: String, error: String },
    KeyUnparseable { key: String },
    FireFailed { key: String, error: String },
    RefreshFailed { error: String },
    ListingFailed { error: String },
    MessageUndeliverable { address: String },
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionNoteData {
    type V = ProductionNoteV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::DocumentWrite { mode, bytes } => ProductionNoteV::DocumentWrite { mode: *mode, bytes: *bytes },
            Self::Commit(o) => ProductionNoteV::Commit(*o),
            Self::Cache(r) => ProductionNoteV::Cache(*r),
            Self::MembershipRefresh { ok } => ProductionNoteV::MembershipRefresh { ok: *ok },
            Self::ConfigurationChange => ProductionNoteV::ConfigurationChange,
            Self::ConfigurationWrite(w) => ProductionNoteV::ConfigurationWrite(*w),
            Self::TimerFire { kind, outcome, lag_ms } => ProductionNoteV::TimerFire { kind: *kind, outcome: *outcome, lag_ms: *lag_ms },
            Self::TimerListing { ok } => ProductionNoteV::TimerListing { ok: *ok },
            Self::Sweep(o) => ProductionNoteV::Sweep(*o),
            Self::SweepBegin { flight, target, now } => ProductionNoteV::SweepBegin { flight: *flight, target: target@, now: *now },
            Self::SweepEnd { flight, committed } => ProductionNoteV::SweepEnd { flight: *flight, committed: *committed },
            Self::FireBegin { flight, origin, now, row, at, promise_id, next } => ProductionNoteV::FireBegin {
                flight: *flight, origin: origin@, now: *now, row: row.deep_view(), at: *at, promise_id: promise_id@, next: *next,
            },
            Self::FireEnd { flight, committed } => ProductionNoteV::FireEnd { flight: *flight, committed: *committed },
            Self::AdvanceBegin { flight, schedule, now, at, next } => ProductionNoteV::AdvanceBegin { flight: *flight, schedule: schedule@, now: *now, at: *at, next: *next },
            Self::AdvanceEnd { flight, committed } => ProductionNoteV::AdvanceEnd { flight: *flight, committed: *committed },
            Self::ConfigurationRead { epoch, members } => ProductionNoteV::ConfigurationRead { epoch: *epoch, members: members.deep_view() },
            Self::ConfigurationWritten { epoch, members } => ProductionNoteV::ConfigurationWritten { epoch: *epoch, members: members.deep_view() },
            Self::TimersLoaded { deadlines, wheel, epoch } => ProductionNoteV::TimersLoaded { deadlines: *deadlines, wheel: *wheel, epoch: *epoch },
            Self::BucketLoaded { bucket, deadlines } => ProductionNoteV::BucketLoaded { bucket: *bucket, deadlines: *deadlines },
            Self::Raced { target, attempt } => ProductionNoteV::Raced { target: target@, attempt: *attempt },
            Self::KeyNotDeleted { key, error } => ProductionNoteV::KeyNotDeleted { key: key@, error: error@ },
            Self::KeyUnparseable { key } => ProductionNoteV::KeyUnparseable { key: key@ },
            Self::FireFailed { key, error } => ProductionNoteV::FireFailed { key: key@, error: error@ },
            Self::RefreshFailed { error } => ProductionNoteV::RefreshFailed { error: error@ },
            Self::ListingFailed { error } => ProductionNoteV::ListingFailed { error: error@ },
            Self::MessageUndeliverable { address } => ProductionNoteV::MessageUndeliverable { address: address@ },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionTargetData {
    Origin(String),
    Schedule(String),
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionTargetData {
    type V = ProductionTargetV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Origin(id) => ProductionTargetV::Origin(id@),
            Self::Schedule(id) => ProductionTargetV::Schedule(id@),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct ProductionCallData {
    pub id: u64,
    pub kind: String,
    pub corr: String,
    pub target: ProductionTargetData,
    pub request: Request,
    pub action_kind: Option<String>,
    pub now: u64,
    pub pinned: bool,
    pub then: Option<(ProductionTargetData, Request)>,
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionCallData {
    type V = ProductionCallV;
    open spec fn deep_view(&self) -> Self::V {
        ProductionCallV {
            id: self.id, kind: self.kind@, corr: self.corr@, target: self.target.deep_view(),
            request: self.request, action_kind: self.action_kind.deep_view(), now: self.now,
            pinned: self.pinned, then: self.then.deep_view(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionDebugInput {
    Reset { id: u64, kind: String, corr: String },
    Snap { id: u64, kind: String, corr: String },
    Tick { id: u64, kind: String, corr: String, time: u64 },
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionDebugInput {
    type V = ProductionDebugCallV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Reset { id, kind, corr } => ProductionDebugCallV::Reset { id: *id, kind: kind@, corr: corr@ },
            Self::Snap { id, kind, corr } => ProductionDebugCallV::Snap { id: *id, kind: kind@, corr: corr@ },
            Self::Tick { id, kind, corr, time } => ProductionDebugCallV::Tick { id: *id, kind: kind@, corr: corr@, time: *time },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum ProductionInput {
    Request { clock: u64, call: ProductionCallData },
    Debug { clock: u64, call: ProductionDebugInput },
    Store { clock: u64, op: u64, response: StoreRes },
    Wake { clock: u64, armed: ProductionArmed },
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionInput {
    type V = ProductionEventV;
    open spec fn deep_view(&self) -> Self::V {
        match self {
            Self::Request { clock, call } => ProductionEventV::Request { clock: *clock, request: ProductionRequestEventV::Protocol(call.deep_view()) },
            Self::Debug { clock, call } => ProductionEventV::Request { clock: *clock, request: ProductionRequestEventV::Debug(call.deep_view()) },
            Self::Store { clock, op, response } => ProductionEventV::Store { clock: *clock, op: *op, response: *response },
            Self::Wake { clock, armed } => ProductionEventV::Wake { clock: *clock, armed: *armed },
        }
    }
}

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

pub enum AJob {
    /// A request: `spec_handle`.
    Request(echod_types::Request),
    /// A fired key: `spec_sweep`, every due step up to a limit.
    Sweep,
    /// A schedule's key: `spec_run_due`, the occurrence due and the schedule advanced.
    Fire,
    /// That occurrence, born in its origin: `spec_occurrence`.
    Occurrence(PendingV),
}

/// The document a step leaves, its answer, the occurrences it queued, and
/// the notes it will send once the document is committed.

pub struct AFired {
    pub key: AKey,
    pub by: Seq<char>,
}

/// Where the commit stands: which call it waits on.

pub enum AStep {
    Start,
    PuttingKey(AKey),
    Writing { idle: bool },
    DeletingPrevious(AKey),
    DeletingFired(AKey),
    Over,
}

/// The commit of one step on one document.

pub struct ASequence {
    pub origin: Seq<char>,
    /// The version loaded; after the write, the version written.
    pub etag: Option<Seq<char>>,
    /// Whether the document differs from what was loaded.
    pub changed: bool,
    pub fired: Option<AFired>,
    /// The token the key armed, if one is, carries.
    pub token: nat,
    pub plan: ACommit,
    pub step: AStep,
}

/// What the shell is asked to do next.

pub enum AAct {
    /// Put the key, empty, and arm the wheel at its instant once it lands.
    PutKey(AKey),
    /// Write the document, conditionally on `cond`: `PutIfMatch` on that
    /// version, `PutIfNoneMatch` when none was loaded. `idle` is a rewrite of
    /// the same rows at a new version, so a fired key can be collected behind it.
    Write { cond: Option<Seq<char>>, idle: bool },
    /// Delete the key `by` armed.
    DeleteKey { key: AKey, by: Seq<char> },
    /// The commit is over; whether the fired key was deleted.
    Done { deleted: bool },
}

/// The store's answer to the call the commit waits on, as the commit reads it.

pub enum AAnswer {
    /// No call was waited on.
    Fresh,
    Done,
    Written(Seq<char>),
    Failed(StoreError),
    /// An answer of another shape.
    Other,
}


pub enum AOutcome {
    Act(AAct),
    /// The store failed the call; `None` is an answer of another shape.
    Failed(Option<StoreError>),
}

pub struct ACommit {
    pub origin: Seq<char>,
    pub deadline: Option<nat>,
    pub changed: bool,
    pub fired: Option<AKey>,
    pub previous: Option<AKey>,
    pub rearm: bool,
    pub armed_now: Option<AKey>,
}

pub struct AKey {
    pub origin: Seq<char>,
    pub at: nat,
    pub token: nat,
}

pub struct AArmed {
    pub key: AKey,
    pub etag: Seq<char>,
}

pub struct AEntry {
    pub etag: Seq<char>,
    pub filled_at: nat,
}

pub struct ANode {
    pub id: Seq<char>,
    pub ttl: nat,
    pub read_any: bool,
    pub epoch: nat,
    pub members: Seq<Seq<char>>,
    pub last_read: nat,
    pub cache: Map<Seq<char>, AEntry>,
    pub armed: Map<Seq<char>, AArmed>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionCachedV {
    pub loaded: LoadedDocumentV,
    pub etag: EtagSpec,
    pub filled_at: u64,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionCacheStatsV {
    pub entries: usize,
    pub bytes: u64,
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionCacheEntryV {
    pub origin: Seq<char>,
    pub cached: ProductionCachedV,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionCacheV {
    pub entries: Seq<ProductionCacheEntryV>,
    pub bytes: u64,
    pub max_entries: usize,
    pub max_bytes: u64,
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
}

pub ghost struct ProductionConfigV {
    pub node_id: Seq<char>,
    pub url: Seq<char>,
    pub prefix: Seq<char>,
    pub compact: u32,
    pub appendable: bool,
    pub retry_timeout: u64,
    pub timer_bucket_ms: u64,
    pub heartbeat_ms: u64,
    pub node_ttl_ms: u64,
    pub cache_entries: usize,
    pub cache_bytes: u64,
    pub debug: bool,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionKeySpaceV {
    pub prefix: Seq<char>,
    pub bucket_ms: u64,
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionTimerEntryV {
    Origin { deadline: u64, origin: Seq<char>, token: u64, by: Seq<char> },
    Schedule { deadline: u64, id: Seq<char>, token: u64, by: Seq<char> },
}





































#[cfg(verus_keep_ghost)]
pub ghost enum ProductionMessageV {
    Execute { task_id: Seq<char>, version: u64 },
    Unblock(PromiseRecordSpec),
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionDebugCallV {
    Reset { id: u64, kind: Seq<char>, corr: Seq<char> },
    Snap { id: u64, kind: Seq<char>, corr: Seq<char> },
    Tick { id: u64, kind: Seq<char>, corr: Seq<char>, time: u64 },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionRequestEventV {
    Protocol(ProductionCallV),
    Debug(ProductionDebugCallV),
}

#[allow(inconsistent_fields)]
#[cfg(verus_keep_ghost)]
pub ghost enum ProductionEventV {
    Request { clock: u64, request: ProductionRequestEventV },
    Store { op: u64, response: StoreRes, clock: u64 },
    Wake { clock: u64, armed: ProductionArmed },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionAnswerV {
    Step { kind: Seq<char>, corr: Seq<char>, action_kind: Option<Seq<char>>, response: AResponse, why: Option<Seq<char>> },
    Debug { kind: Seq<char>, corr: Seq<char>, status: u16, body: ProductionDebugBodyV },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionDebugBodyV {
    Object,
    List,
    Message(Seq<char>),
    Snap { origins: Seq<DocumentBodyV>, schedules: Seq<ScheduleSpec> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionEffectV {
    Reply { id: u64, response: Result<ProductionAnswerV, Seq<char>> },
    Store { op: u64, request: StoreReqSpec },
    Wake { after_ms: u64, armed: ProductionArmed },
    Send { address: Seq<char>, message: ProductionMessageV },
    Note(ProductionNoteV),
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionNoteV {
    DocumentWrite { mode: ProductionWriteMode, bytes: usize },
    Commit(ProductionCommitOutcome),
    Cache(ProductionCacheResult),
    MembershipRefresh { ok: bool },
    ConfigurationChange,
    ConfigurationWrite(ProductionConfigWrite),
    TimerFire { kind: ProductionTimerKind, outcome: ProductionFireOutcome, lag_ms: u64 },
    TimerListing { ok: bool },
    Sweep(ProductionSweepOutcome),
    SweepBegin { flight: u64, target: Seq<char>, now: u64 },
    SweepEnd { flight: u64, committed: bool },
    FireBegin { flight: u64, origin: Seq<char>, now: u64, row: ScheduleSpec, at: u64, promise_id: Seq<char>, next: u64 },
    FireEnd { flight: u64, committed: bool },
    AdvanceBegin { flight: u64, schedule: Seq<char>, now: u64, at: u64, next: u64 },
    AdvanceEnd { flight: u64, committed: bool },
    ConfigurationRead { epoch: u64, members: Seq<Seq<char>> },
    ConfigurationWritten { epoch: u64, members: Seq<Seq<char>> },
    TimersLoaded { deadlines: usize, wheel: usize, epoch: u64 },
    BucketLoaded { bucket: u64, deadlines: usize },
    Raced { target: Seq<char>, attempt: u32 },
    KeyNotDeleted { key: Seq<char>, error: Seq<char> },
    KeyUnparseable { key: Seq<char> },
    FireFailed { key: Seq<char>, error: Seq<char> },
    RefreshFailed { error: Seq<char> },
    ListingFailed { error: Seq<char> },
    MessageUndeliverable { address: Seq<char> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionTargetV {
    Origin(Seq<char>),
    Schedule(Seq<char>),
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionCallV {
    pub id: u64,
    pub kind: Seq<char>,
    pub corr: Seq<char>,
    pub target: ProductionTargetV,
    pub request: Request,
    pub action_kind: Option<Seq<char>>,
    pub now: u64,
    pub pinned: bool,
    pub then: Option<(ProductionTargetV, Request)>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionAnnouncementV {
    pub id: Seq<char>,
    pub url: Seq<char>,
    pub at: u64,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionConfigurationV {
    pub epoch: u64,
    pub members: Seq<Seq<char>>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionRosterV {
    pub entries: Seq<(Seq<char>, ProductionAnnouncementV)>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionMembersV {
    pub me: ProductionAnnouncementV,
    pub heartbeat_ms: u64,
    pub ttl: u64,
    pub nodes: ProductionRosterV,
    pub etag: Option<EtagSpec>,
    pub next_heartbeat: Option<u64>,
    pub refresh: Option<ProductionRefreshV>,
    pub read_once: bool,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionNodeStateV {
    pub core: ANode,
    pub members: ProductionMembersV,
    pub fleet_at: u64,
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionRefreshV {
    Announcing { op: u64, now: u64 },
    Listing { op: u64, now: u64 },
    Reading { pending: Map<u64, bool>, nodes: ProductionRosterV, now: u64, failed: Option<StoreErrorSpec> },
    Config { op: u64, nodes: ProductionRosterV },
    Writing { op: u64, next: ProductionConfigurationV },
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionTimerWheelV {
    pub armed: Seq<(u64, Seq<char>)>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionTimersV {
    pub wheel: ProductionTimerWheelV,
    pub started: bool,
    pub loaded_through: Option<u64>,
    pub closed_through: Option<u64>,
    pub bucket_ms: u64,
    pub reload_pending: bool,
    pub listing: Option<ProductionListingV>,
    pub backoff_until: Option<u64>,
    pub inflight: usize,
    pub backlog: Seq<(u64, Seq<char>)>,
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionListingV {
    Prefixes { op: u64, horizon: u64 },
    Buckets { pending: Map<u64, u64>, horizon: u64, loaded: usize, failed: Option<StoreErrorSpec> },
    Extend { op: u64, bucket: u64 },
    Relist { op: u64, bucket: u64 },
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionFiringV {
    pub key: Seq<char>,
    pub at: u64,
    pub kind: ProductionTimerKind,
    pub lag: u64,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionWorkingV {
    pub target: Seq<char>,
    pub key: Seq<char>,
    pub loaded: LoadedDocumentV,
    pub etag: Option<EtagSpec>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionCommittingV {
    pub w: ProductionWorkingV,
    pub after: StoredDocumentV,
    pub now: u64,
    pub seq: ASequence,
    pub issued: Option<ProductionIssuedV>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionDoneV {
    pub response: Option<AResponse>,
    pub why: Option<Seq<char>>,
    pub outbox: Seq<(Seq<char>, ProductionMessageV)>,
    pub did: bool,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionFireCtxV {
    pub ws: ProductionWorkingV,
    pub row: ScheduleSpec,
    pub advanced: DocumentBodyV,
    pub pending: PendingV,
    pub t1: u64,
    pub origin: Seq<char>,
    pub next: u64,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionFlightV {
    pub id: u64,
    pub target: ProductionTargetV,
    pub work: ProductionWorkV,
    pub attempt: u32,
    pub phase: ProductionPhaseV,
    pub firing: Option<ProductionFiringV>,
    pub debug: bool,
    pub idle: bool,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionDocumentSlotV {
    pub busy: Option<u64>,
    pub queue: Seq<ProductionQueuedV>,
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionFlightsV {
    pub slots: Map<Seq<char>, ProductionDocumentSlotV>,
    pub inflight: Map<u64, ProductionFlightV>,
    pub max_retries: u32,
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionWorkV {
    Request { id: u64, kind: Seq<char>, corr: Seq<char>, req: Request, action_kind: Option<Seq<char>>, now: u64, stage: ProductionStageV },
    Sweep { fired: Option<AFired>, now: u64 },
    Fire { schedule: Seq<char>, fired: Option<AFired>, now: u64 },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionStageV {
    Whole,
    Detached { then: ProductionTargetV, check: Option<Request> },
    Check { inner: Option<PromiseResSpec> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionIssuedV {
    Key { op: u64, key: AKey, name: Seq<char>, arm: bool },
    Write { op: u64, mode: ProductionWriteMode, change_count: usize, bytes: u64, len: usize },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionProgressV {
    Issued,
    Done(ProductionFired),
    Failed(StoreErrorSpec),
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionPhaseV {
    Idle,
    Loading { op: u64, revalidating: Option<ProductionCachedV> },
    Origin { commit: ProductionCommittingV, done: ProductionDoneV },
    Schedule { commit: ProductionCommittingV, done: ProductionDoneV },
    FireLoadingSchedule { op: u64 },
    FireWaitingOrigin(ProductionFireCtxV),
    FireLoadingOrigin { op: u64, revalidating: Option<ProductionCachedV>, ctx: ProductionFireCtxV },
    FireIdle { commit: ProductionCommittingV },
    FireOrigin { commit: ProductionCommittingV, ctx: ProductionFireCtxV, t: u64 },
    FireSchedule { commit: ProductionCommittingV },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionQueuedV {
    Work { target: ProductionTargetV, work: ProductionWorkV, firing: Option<ProductionFiringV>, debug: bool },
    Waiter(u64),
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionDebugV {
    pub current: Option<ProductionDebugOpV>,
    pub queue: Seq<ProductionDebugCallV>,
}

#[allow(inconsistent_fields)]
#[cfg(verus_keep_ghost)]
pub ghost enum ProductionDebugOpV {
    Reset { id: u64, kind: Seq<char>, corr: Seq<char>, phase: ProductionDebugResetV },
    Snap { id: u64, kind: Seq<char>, corr: Seq<char>, phase: ProductionDebugSnapV },
    Tick { id: u64, kind: Seq<char>, corr: Seq<char>, time: u64, phase: ProductionDebugTickV },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionDebugResetV {
    Listing { op: u64 },
    Deleting { pending: Map<u64, bool> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionDebugSnapV {
    Gathering { ops: Map<u64, bool>, pending: Map<u64, bool>, origins: Seq<DocumentBodyV>, schedules: Seq<ScheduleSpec> },
}

#[cfg(verus_keep_ghost)]
pub ghost enum ProductionDebugTickV {
    Listing { ops: Map<u64, bool>, origins: Seq<Seq<char>>, schedules: Seq<Seq<char>> },
    Sweeping { outstanding: usize, schedules: Seq<Seq<char>> },
    Firing { outstanding: usize },
}

#[cfg(verus_keep_ghost)]
pub ghost struct ProductionStateV {
    pub cfg: ProductionConfigV,
    pub keys: ProductionKeySpaceV,
    pub node: ProductionNodeStateV,
    pub timers: ProductionTimersV,
    pub cache: ProductionCacheV,
    pub clock: u64,
    pub tokens: u64,
    pub next_op: u64,
    pub next_flight: u64,
    pub ops: Map<u64, ProductionOwner>,
    pub flights: ProductionFlightsV,
    pub debug: ProductionDebugV,
    pub loops: bool,
    pub out: Seq<ProductionEffectV>,
    pub last_wake: Option<(u64, ProductionArmed)>,
}

pub const RETRY_AFTER_MS: u64 = 1_000;
pub const RELIST_AFTER_MS: u64 = 1_000;
pub const CONCURRENCY: usize = 16;

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
