//! What an operator sees: OpenMetrics at `GET /metrics`.
//!
//! The rule for every label here: its values are a closed set the server
//! decides, never a name a client or the bucket supplies. No origin, no
//! promise id, no key, no address, no error text, no node id is a label;
//! those go to the logs. What is left tells an operator what is happening
//! and where the time goes, at a cardinality that stays flat however many
//! promises there are.
//!
//! ```text
//! requests     echod_requests_total{kind,route,status}          every request, by what it was,
//!              echod_request_duration_seconds{kind,route}        where it ran, and how it ended
//! peers        echod_forwards_total{outcome}                     requests sent to the owner node
//!              echod_forward_duration_seconds
//! messages     echod_messages_total{kind,outcome}                pushes to workers
//!              echod_message_duration_seconds
//! store        echod_store_operations_total{op,object,outcome}  every call on the bucket: the
//!              echod_store_operation_duration_seconds{op,object} operation, the kind of object, and
//!                                                                whether it applied, was CAS'ed out
//!                                                                (`conflict`), or failed with an
//!                                                                unknown effect
//! documents    echod_document_writes_total{mode}                 create, rewrite, append
//!              echod_document_bytes                              what a write put down
//!              echod_commits_total{outcome}                      committed, raced, failed, exhausted
//! cache        echod_cache_lookups_total{result}                 revalidated, refreshed, absent, miss
//!              echod_cache_entries, echod_cache_bytes,
//!              echod_cache_evictions_total
//! membership   echod_membership_refreshes_total{outcome}
//!              echod_configuration_changes_total                 ownership moved
//!              echod_configuration_writes_total{outcome}
//!              echod_membership_epoch, echod_members,
//!              echod_node_fresh, echod_node_acting
//! timers       echod_timer_fires_total{kind,outcome}
//!              echod_timer_lag_seconds{kind}                     how late a deadline fired
//!              echod_timer_listings_total{outcome}
//!              echod_timers_armed
//!              echod_sweeps_total{outcome}                       fired, idle, failed
//! build        echod_build_info{version}
//! ```

use std::sync::{Arc, Mutex};
use std::time::Instant;

use async_trait::async_trait;
use prometheus_client::collector::Collector;
use prometheus_client::encoding::{DescriptorEncoder, EncodeLabelSet, EncodeLabelValue, EncodeMetric, LabelValueEncoder};
use prometheus_client::metrics::counter::{ConstCounter, Counter};
use prometheus_client::metrics::family::Family;
use prometheus_client::metrics::gauge::ConstGauge;
use prometheus_client::metrics::histogram::{exponential_buckets, Histogram};
use prometheus_client::metrics::info::Info;
use prometheus_client::registry::Registry;

use crate::keys::KeySpace;
use crate::store::{Etag, Read, Store, StoreError};

/// The content type of what `encode` produces.
pub const CONTENT_TYPE: &str = "application/openmetrics-text; version=1.0.0; charset=utf-8";

/// An enum whose variants are a label's values, written in lower case.
macro_rules! label {
    ($(#[$m:meta])* $name:ident { $($variant:ident => $text:literal),+ $(,)? }) => {
        $(#[$m])*
        #[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
        pub enum $name { $($variant),+ }

        impl $name {
            pub fn as_str(self) -> &'static str {
                match self { $(Self::$variant => $text),+ }
            }
        }

        impl EncodeLabelValue for $name {
            fn encode(&self, e: &mut LabelValueEncoder) -> Result<(), std::fmt::Error> {
                use std::fmt::Write;
                e.write_str(self.as_str())
            }
        }
    };
}

label! {
    /// Where a request ran: here for its own client, here for another node
    /// that relayed it, or at the owner it was forwarded to.
    Route { Local => "local", Relayed => "relayed", Forwarded => "forwarded" }
}

label! {
    /// How a call to another node ended.
    ForwardOutcome { Answered => "answered", Unavailable => "unavailable" }
}

label! {
    /// What was pushed to a worker.
    MessageKind { Execute => "execute", Unblock => "unblock", Other => "other" }
}

label! {
    MessageOutcome { Delivered => "delivered", Unroutable => "unroutable", Failed => "failed" }
}

label! {
    /// A call on the store.
    StoreOp {
        Get => "get",
        GetIfNoneMatch => "get_if_none_match",
        Put => "put",
        PutIfMatch => "put_if_match",
        PutIfNoneMatch => "put_if_none_match",
        AppendIfMatch => "append_if_match",
        Delete => "delete",
        List => "list",
        ListPrefixes => "list_prefixes",
    }
}

label! {
    /// The kind of object a key names, by where it lives in the bucket.
    Object { Document => "document", Schedule => "schedule", Timer => "timer", Node => "node", Members => "members", Other => "other" }
}

label! {
    /// How a store call ended. A write that `failed` may or may not have
    /// landed; `conflict` is a conditional write the store refused because
    /// the object had moved: CAS'ed out.
    StoreOutcome { Ok => "ok", NotModified => "not_modified", Absent => "absent", Conflict => "conflict", Failed => "failed" }
}

label! {
    WriteMode { Create => "create", Rewrite => "rewrite", Append => "append" }
}

label! {
    /// How an attempt to commit a step ended: it landed; it lost a race on
    /// the document and was re-decided; the store failed; or the races ran
    /// out.
    CommitOutcome { Committed => "committed", Raced => "raced", Failed => "failed", Exhausted => "exhausted" }
}

label! {
    /// What a lookup in the document cache cost. `revalidated`: a
    /// conditional read confirmed the version held, and the body in memory
    /// was used. `refreshed`: the conditional read brought a newer version.
    /// `absent`: the document is gone from the bucket. `miss`: nothing was
    /// held; a full read.
    CacheResult { Revalidated => "revalidated", Refreshed => "refreshed", Absent => "absent", Miss => "miss" }
}

label! {
    Outcome { Ok => "ok", Failed => "failed" }
}

label! {
    ConfigWrite { Written => "written", Conflict => "conflict", Failed => "failed" }
}

label! {
    TimerKind { Origin => "origin", Schedule => "schedule" }
}

label! {
    /// What became of a fired key: deleted after its sweep committed; kept,
    /// to fire again, because the delete failed; the sweep failed; or it
    /// was deferred because this node does not act on its target right now.
    FireOutcome { Deleted => "deleted", Kept => "kept", Failed => "failed", Deferred => "deferred" }
}

label! {
    /// A sweep fired something, found nothing due, or did not commit.
    SweepOutcome { Fired => "fired", Idle => "idle", Failed => "failed" }
}

/// The request kinds the protocol defines; anything else is `other`, so a
/// client cannot mint label values.
const KINDS: &[&str] = &[
    "promise.get",
    "promise.create",
    "promise.settle",
    "promise.register_callback",
    "promise.register_listener",
    "promise.search",
    "task.get",
    "task.create",
    "task.acquire",
    "task.release",
    "task.fulfill",
    "task.suspend",
    "task.fence",
    "task.heartbeat",
    "task.halt",
    "task.continue",
    "task.search",
    "schedule.get",
    "schedule.create",
    "schedule.delete",
    "schedule.search",
];

/// The label value for a request kind: the kind if the protocol knows it.
pub fn kind_label(kind: &str) -> &'static str {
    KINDS.iter().copied().find(|k| *k == kind).unwrap_or("other")
}

pub fn message_kind(kind: &str) -> MessageKind {
    match kind {
        "execute" => MessageKind::Execute,
        "unblock" => MessageKind::Unblock,
        _ => MessageKind::Other,
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct RequestLabels {
    pub kind: &'static str,
    pub route: Route,
    pub status: u16,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct RequestTiming {
    pub kind: &'static str,
    pub route: Route,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct ForwardLabels {
    pub outcome: ForwardOutcome,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct MessageLabels {
    pub kind: MessageKind,
    pub outcome: MessageOutcome,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct StoreLabels {
    pub op: StoreOp,
    pub object: Object,
    pub outcome: StoreOutcome,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct StoreTiming {
    pub op: StoreOp,
    pub object: Object,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct ModeLabels {
    pub mode: WriteMode,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct CommitLabels {
    pub outcome: CommitOutcome,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct CacheLabels {
    pub result: CacheResult,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct OutcomeLabels {
    pub outcome: Outcome,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct ConfigWriteLabels {
    pub outcome: ConfigWrite,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct FireLabels {
    pub kind: TimerKind,
    pub outcome: FireOutcome,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct TimerKindLabels {
    pub kind: TimerKind,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
pub struct SweepLabels {
    pub outcome: SweepOutcome,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
struct BuildLabels {
    version: &'static str,
}

/// What the gauges read at scrape time: the state the node is in now, not
/// a count of what happened. Supplied by whoever owns the state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Snapshot {
    pub cache_entries: u64,
    pub cache_bytes: u64,
    pub cache_evictions: u64,
    pub epoch: u64,
    pub members: u64,
    pub fresh: bool,
    pub acting: bool,
    pub timers_armed: u64,
}

type SnapshotFn = Box<dyn Fn() -> Snapshot + Send + Sync>;

/// Encodes the snapshot on every scrape.
struct Gauges(Arc<Mutex<Option<SnapshotFn>>>);

impl std::fmt::Debug for Gauges {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Gauges")
    }
}

impl Collector for Gauges {
    fn encode(&self, mut encoder: DescriptorEncoder) -> Result<(), std::fmt::Error> {
        let snap = match self.0.lock().unwrap_or_else(|e| e.into_inner()).as_ref() {
            Some(f) => f(),
            None => return Ok(()),
        };
        let gauge = |encoder: &mut DescriptorEncoder, name: &str, help: &str, v: u64| -> Result<(), std::fmt::Error> {
            let g = ConstGauge::new(v as i64);
            let e = encoder.encode_descriptor(name, help, None, g.metric_type())?;
            g.encode(e)
        };
        gauge(&mut encoder, "echod_cache_entries", "Documents held in the cache.", snap.cache_entries)?;
        gauge(&mut encoder, "echod_cache_bytes", "Bytes of documents held in the cache, by object size.", snap.cache_bytes)?;
        {
            let c = ConstCounter::new(snap.cache_evictions);
            let e = encoder.encode_descriptor("echod_cache_evictions", "Documents evicted from the cache to make room.", None, c.metric_type())?;
            c.encode(e)?;
        }
        gauge(&mut encoder, "echod_membership_epoch", "The epoch of the configuration this node holds.", snap.epoch)?;
        gauge(&mut encoder, "echod_members", "Members in the configuration this node holds.", snap.members)?;
        gauge(&mut encoder, "echod_node_fresh", "Whether this node's view of the membership is fresh enough to serve.", snap.fresh as u64)?;
        gauge(&mut encoder, "echod_node_acting", "Whether this node acts as owner of what the members make it the owner of: it routes.", snap.acting as u64)?;
        gauge(&mut encoder, "echod_timers_armed", "Deadline keys held in the wheel.", snap.timers_armed)?;
        Ok(())
    }
}

pub struct Metrics {
    registry: Registry,
    snapshot: Arc<Mutex<Option<SnapshotFn>>>,
    pub requests: Family<RequestLabels, Counter>,
    pub request_duration: Family<RequestTiming, Histogram>,
    pub forwards: Family<ForwardLabels, Counter>,
    pub forward_duration: Histogram,
    pub messages: Family<MessageLabels, Counter>,
    pub message_duration: Histogram,
    pub store_operations: Family<StoreLabels, Counter>,
    pub store_duration: Family<StoreTiming, Histogram>,
    pub document_writes: Family<ModeLabels, Counter>,
    pub document_bytes: Histogram,
    pub commits: Family<CommitLabels, Counter>,
    pub cache_lookups: Family<CacheLabels, Counter>,
    pub membership_refreshes: Family<OutcomeLabels, Counter>,
    pub configuration_changes: Counter,
    pub configuration_writes: Family<ConfigWriteLabels, Counter>,
    pub timer_fires: Family<FireLabels, Counter>,
    pub timer_lag: Family<TimerKindLabels, Histogram>,
    pub timer_listings: Family<OutcomeLabels, Counter>,
    pub sweeps: Family<SweepLabels, Counter>,
}

/// Latencies from a quarter of a millisecond to about a minute.
fn latency() -> Histogram {
    Histogram::new(exponential_buckets(0.00025, 2.0, 18))
}

/// Sizes from 256 bytes to about 256 MiB.
fn size() -> Histogram {
    Histogram::new(exponential_buckets(256.0, 4.0, 11))
}

/// Lags from a millisecond to about an hour.
fn lag() -> Histogram {
    Histogram::new(exponential_buckets(0.001, 4.0, 12))
}

impl Metrics {
    pub fn new() -> Arc<Self> {
        let mut registry = Registry::default();
        let snapshot: Arc<Mutex<Option<SnapshotFn>>> = Arc::new(Mutex::new(None));

        let requests = Family::<RequestLabels, Counter>::default();
        registry.register("echod_requests", "Requests, by kind, where they ran, and the status answered", requests.clone());
        let request_duration = Family::<RequestTiming, Histogram>::new_with_constructor(latency);
        registry.register_with_unit("echod_request_duration", "Time from receiving a request to answering it", prometheus_client::registry::Unit::Seconds, request_duration.clone());

        let forwards = Family::<ForwardLabels, Counter>::default();
        registry.register("echod_forwards", "Requests forwarded to the node that owns their origin", forwards.clone());
        let forward_duration = latency();
        registry.register_with_unit("echod_forward_duration", "Round trip of a request forwarded to another node", prometheus_client::registry::Unit::Seconds, forward_duration.clone());

        let messages = Family::<MessageLabels, Counter>::default();
        registry.register("echod_messages", "Messages pushed to workers", messages.clone());
        let message_duration = latency();
        registry.register_with_unit("echod_message_duration", "Round trip of a push to a worker", prometheus_client::registry::Unit::Seconds, message_duration.clone());

        let store_operations = Family::<StoreLabels, Counter>::default();
        registry.register("echod_store_operations", "Calls on the object store, by operation, the kind of object, and how they ended; a conditional write the store refused is a conflict, a failed write may or may not have landed", store_operations.clone());
        let store_duration = Family::<StoreTiming, Histogram>::new_with_constructor(latency);
        registry.register_with_unit("echod_store_operation_duration", "Round trip of a call on the object store", prometheus_client::registry::Unit::Seconds, store_duration.clone());

        let document_writes = Family::<ModeLabels, Counter>::default();
        registry.register("echod_document_writes", "Documents written, by whether they were created, rewritten, or appended to", document_writes.clone());
        let document_bytes = size();
        registry.register_with_unit("echod_document", "Bytes put down by a document write", prometheus_client::registry::Unit::Bytes, document_bytes.clone());
        let commits = Family::<CommitLabels, Counter>::default();
        registry.register("echod_commits", "Attempts to commit a step on a document, by how they ended", commits.clone());

        let cache_lookups = Family::<CacheLabels, Counter>::default();
        registry.register("echod_cache_lookups", "Document loads, by what they cost: revalidated, refreshed, absent, or a miss", cache_lookups.clone());

        let membership_refreshes = Family::<OutcomeLabels, Counter>::default();
        registry.register("echod_membership_refreshes", "Heartbeats: announce, list the nodes, read the configuration", membership_refreshes.clone());
        let configuration_changes = Counter::default();
        registry.register("echod_configuration_changes", "Configurations taken on with a new epoch: ownership moved", configuration_changes.clone());
        let configuration_writes = Family::<ConfigWriteLabels, Counter>::default();
        registry.register("echod_configuration_writes", "Attempts to write the next configuration", configuration_writes.clone());

        let timer_fires = Family::<FireLabels, Counter>::default();
        registry.register("echod_timer_fires", "Deadline keys fired from the wheel, by what became of them", timer_fires.clone());
        let timer_lag = Family::<TimerKindLabels, Histogram>::new_with_constructor(lag);
        registry.register_with_unit("echod_timer_lag", "How long after its deadline a key fired", prometheus_client::registry::Unit::Seconds, timer_lag.clone());
        let timer_listings = Family::<OutcomeLabels, Counter>::default();
        registry.register("echod_timer_listings", "Listings of timer buckets: at startup, on a change of membership, and when the clock reaches a new bucket", timer_listings.clone());
        let sweeps = Family::<SweepLabels, Counter>::default();
        registry.register("echod_sweeps", "Sweeps of an origin for what is due, by whether they fired anything", sweeps.clone());

        registry.register("echod_build", "The build", Info::new(BuildLabels { version: env!("CARGO_PKG_VERSION") }));
        registry.register_collector(Box::new(Gauges(Arc::clone(&snapshot))));

        Arc::new(Self {
            registry,
            snapshot,
            requests,
            request_duration,
            forwards,
            forward_duration,
            messages,
            message_duration,
            store_operations,
            store_duration,
            document_writes,
            document_bytes,
            commits,
            cache_lookups,
            membership_refreshes,
            configuration_changes,
            configuration_writes,
            timer_fires,
            timer_lag,
            timer_listings,
            sweeps,
        })
    }

    /// Supply what the gauges read at scrape time.
    pub fn set_snapshot(&self, f: impl Fn() -> Snapshot + Send + Sync + 'static) {
        *self.snapshot.lock().unwrap_or_else(|e| e.into_inner()) = Some(Box::new(f));
    }

    /// The OpenMetrics text exposition.
    pub fn encode(&self) -> String {
        let mut out = String::new();
        prometheus_client::encoding::text::encode(&mut out, &self.registry).expect("metrics encode");
        out
    }

    pub fn request(&self, kind: &str, route: Route, status: u16, started: Instant) {
        let kind = kind_label(kind);
        self.requests.get_or_create(&RequestLabels { kind, route, status }).inc();
        self.request_duration.get_or_create(&RequestTiming { kind, route }).observe(started.elapsed().as_secs_f64());
    }

    pub fn forward(&self, outcome: ForwardOutcome, started: Instant) {
        self.forwards.get_or_create(&ForwardLabels { outcome }).inc();
        self.forward_duration.observe(started.elapsed().as_secs_f64());
    }

    pub fn message(&self, kind: &str, outcome: MessageOutcome, started: Instant) {
        self.messages.get_or_create(&MessageLabels { kind: message_kind(kind), outcome }).inc();
        self.message_duration.observe(started.elapsed().as_secs_f64());
    }

    pub fn store(&self, op: StoreOp, object: Object, outcome: StoreOutcome, started: Instant) {
        self.store_operations.get_or_create(&StoreLabels { op, object, outcome }).inc();
        self.store_duration.get_or_create(&StoreTiming { op, object }).observe(started.elapsed().as_secs_f64());
    }

    pub fn document_write(&self, mode: WriteMode, bytes: usize) {
        self.document_writes.get_or_create(&ModeLabels { mode }).inc();
        self.document_bytes.observe(bytes as f64);
    }

    pub fn commit(&self, outcome: CommitOutcome) {
        self.commits.get_or_create(&CommitLabels { outcome }).inc();
    }

    pub fn cache(&self, result: CacheResult) {
        self.cache_lookups.get_or_create(&CacheLabels { result }).inc();
    }

    pub fn membership_refresh(&self, ok: bool) {
        self.membership_refreshes.get_or_create(&OutcomeLabels { outcome: if ok { Outcome::Ok } else { Outcome::Failed } }).inc();
    }

    pub fn configuration_change(&self) {
        self.configuration_changes.inc();
    }

    pub fn configuration_write(&self, outcome: ConfigWrite) {
        self.configuration_writes.get_or_create(&ConfigWriteLabels { outcome }).inc();
    }

    /// A key fired: what became of it, and how late it was, in ms.
    pub fn timer_fire(&self, kind: TimerKind, outcome: FireOutcome, lag_ms: u64) {
        self.timer_fires.get_or_create(&FireLabels { kind, outcome }).inc();
        self.timer_lag.get_or_create(&TimerKindLabels { kind }).observe(lag_ms as f64 / 1000.0);
    }

    pub fn timer_listing(&self, ok: bool) {
        self.timer_listings.get_or_create(&OutcomeLabels { outcome: if ok { Outcome::Ok } else { Outcome::Failed } }).inc();
    }

    pub fn sweep(&self, outcome: SweepOutcome) {
        self.sweeps.get_or_create(&SweepLabels { outcome }).inc();
    }
}

impl std::fmt::Debug for Metrics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Metrics")
    }
}

// ---------------------------------------------------------------------------
// The store, observed
// ---------------------------------------------------------------------------

/// A store that counts and times every call on the one behind it. The
/// object's kind comes from the key's place in the bucket; the key itself
/// is never a label.
pub struct MeteredStore {
    inner: Arc<dyn Store>,
    keys: KeySpace,
    metrics: Arc<Metrics>,
}

impl MeteredStore {
    pub fn new(inner: Arc<dyn Store>, keys: KeySpace, metrics: Arc<Metrics>) -> Self {
        Self { inner, keys, metrics }
    }

    fn object(&self, key: &str) -> Object {
        match self.keys.class_of(key) {
            Some("wf") => Object::Document,
            Some("sched") => Object::Schedule,
            Some("t") => Object::Timer,
            Some("nodes") => Object::Node,
            Some("members") => Object::Members,
            _ => Object::Other,
        }
    }

    fn done<T>(&self, op: StoreOp, key: &str, started: Instant, r: &Result<T, StoreError>, ok: impl FnOnce(&T) -> StoreOutcome) {
        let outcome = match r {
            Ok(v) => ok(v),
            Err(StoreError::PreconditionFailed) => StoreOutcome::Conflict,
            Err(StoreError::Unavailable(_)) => StoreOutcome::Failed,
        };
        self.metrics.store(op, self.object(key), outcome, started);
    }
}

#[async_trait]
impl Store for MeteredStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        let t = Instant::now();
        let r = self.inner.get(key).await;
        self.done(StoreOp::Get, key, t, &r, |v| if v.is_some() { StoreOutcome::Ok } else { StoreOutcome::Absent });
        r
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        let t = Instant::now();
        let r = self.inner.get_if_none_match(key, etag).await;
        self.done(StoreOp::GetIfNoneMatch, key, t, &r, |v| match v {
            Read::Body(..) => StoreOutcome::Ok,
            Read::NotModified => StoreOutcome::NotModified,
            Read::Absent => StoreOutcome::Absent,
        });
        r
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        let t = Instant::now();
        let r = self.inner.put_if_match(key, body, etag).await;
        self.done(StoreOp::PutIfMatch, key, t, &r, |_| StoreOutcome::Ok);
        r
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        let t = Instant::now();
        let r = self.inner.put_if_none_match(key, body).await;
        self.done(StoreOp::PutIfNoneMatch, key, t, &r, |_| StoreOutcome::Ok);
        r
    }

    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        let t = Instant::now();
        let r = self.inner.append_if_match(key, offset, body, etag).await;
        self.done(StoreOp::AppendIfMatch, key, t, &r, |_| StoreOutcome::Ok);
        r
    }

    fn supports_append(&self) -> bool {
        self.inner.supports_append()
    }

    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        let t = Instant::now();
        let r = self.inner.put(key, body).await;
        self.done(StoreOp::Put, key, t, &r, |_| StoreOutcome::Ok);
        r
    }

    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        let t = Instant::now();
        let r = self.inner.delete(key).await;
        self.done(StoreOp::Delete, key, t, &r, |_| StoreOutcome::Ok);
        r
    }

    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        let t = Instant::now();
        let r = self.inner.list(prefix, max_keys).await;
        self.done(StoreOp::List, prefix, t, &r, |_| StoreOutcome::Ok);
        r
    }

    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        let t = Instant::now();
        let r = self.inner.list_prefixes(prefix).await;
        self.done(StoreOp::ListPrefixes, prefix, t, &r, |_| StoreOutcome::Ok);
        r
    }

    async fn ready(&self) -> bool {
        self.inner.ready().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::MemoryStore;

    #[test]
    fn a_client_cannot_mint_a_kind() {
        assert_eq!(kind_label("promise.create"), "promise.create");
        assert_eq!(kind_label("promise.create; DROP TABLE"), "other");
        assert_eq!(kind_label(""), "other");
    }

    #[tokio::test]
    async fn the_store_is_counted_by_object_and_outcome() {
        let m = Metrics::new();
        let keys = KeySpace::new("pre", 1000);
        let s = MeteredStore::new(Arc::new(MemoryStore::new()), keys.clone(), Arc::clone(&m));
        let doc = keys.doc_key("o");
        let v1 = s.put_if_none_match(&doc, b"one".to_vec()).await.unwrap();
        assert_eq!(s.put_if_none_match(&doc, b"again".to_vec()).await, Err(StoreError::PreconditionFailed));
        let _v2 = s.put_if_match(&doc, b"two".to_vec(), &v1).await.unwrap();
        assert_eq!(s.put_if_match(&doc, b"three".to_vec(), &v1).await, Err(StoreError::PreconditionFailed), "CAS'ed out");
        assert!(matches!(s.get_if_none_match(&doc, &v1).await.unwrap(), Read::Body(..)));
        assert!(s.get(&keys.doc_key("nobody")).await.unwrap().is_none());
        s.put(&keys.timer_key("o", 5, 1, "n"), Vec::new()).await.unwrap();
        s.list(&keys.timer_prefix(), 10).await.unwrap();
        s.put(&keys.members_key(), b"{}".to_vec()).await.unwrap();

        let text = m.encode();
        let line = |l: &str| assert!(text.contains(l), "missing {l:?} in\n{text}");
        line(r#"echod_store_operations_total{op="put_if_none_match",object="document",outcome="ok"} 1"#);
        line(r#"echod_store_operations_total{op="put_if_none_match",object="document",outcome="conflict"} 1"#);
        line(r#"echod_store_operations_total{op="put_if_match",object="document",outcome="ok"} 1"#);
        line(r#"echod_store_operations_total{op="put_if_match",object="document",outcome="conflict"} 1"#);
        line(r#"echod_store_operations_total{op="get_if_none_match",object="document",outcome="ok"} 1"#);
        line(r#"echod_store_operations_total{op="get",object="document",outcome="absent"} 1"#);
        line(r#"echod_store_operations_total{op="put",object="timer",outcome="ok"} 1"#);
        line(r#"echod_store_operations_total{op="list",object="timer",outcome="ok"} 1"#);
        line(r#"echod_store_operations_total{op="put",object="members",outcome="ok"} 1"#);
        line(r#"echod_store_operation_duration_seconds_count{op="put_if_match",object="document"} 2"#);
        assert!(!text.contains("pre/wf/o"), "a key is never a label");
        assert!(text.ends_with("# EOF\n"));
    }

    #[test]
    fn the_gauges_read_the_snapshot() {
        let m = Metrics::new();
        assert!(!m.encode().contains("echod_cache_entries"), "no snapshot, no gauges");
        m.set_snapshot(|| Snapshot { cache_entries: 3, cache_bytes: 400, cache_evictions: 1, epoch: 7, members: 2, fresh: true, acting: false, timers_armed: 9 });
        let text = m.encode();
        for l in ["echod_cache_entries 3", "echod_cache_bytes 400", "echod_cache_evictions_total 1", "echod_membership_epoch 7", "echod_members 2", "echod_node_fresh 1", "echod_node_acting 0", "echod_timers_armed 9"] {
            assert!(text.contains(l), "missing {l:?} in\n{text}");
        }
    }
}
