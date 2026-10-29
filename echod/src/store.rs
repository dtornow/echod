//! The object store port.
//!
//! Every write that commits state is conditional on the version the writer
//! read: `If-Match` on the ETag, or `If-None-Match: *` for a fresh key. A
//! directory bucket also appends; a general-purpose bucket rewrites. Timer and
//! node objects carry their meaning in the key and are written blind.

use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use echod_concrete::raw::{ConditionalRead as RawRead, Failure, Key, Operation, RawStore, Response};

pub use echod_concrete::raw::Environment;
pub use echod_logic::types::{Etag, Read, StoreCall, StoreError, StoreOutcome};

#[async_trait]
pub trait Store: Send + Sync {
    /// Read an object and its version.
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError>;

    /// Read an object unless it is still at `etag`.
    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError>;

    /// Replace the object only if it is still at `etag`.
    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError>;

    /// Create the object only if nothing is there.
    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError>;

    /// Append `body` to the object only if it is still at `etag`, at byte
    /// `offset`, its current size. Directory buckets only.
    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError>;

    /// Whether `append_if_match` is available.
    fn supports_append(&self) -> bool;

    /// Write unconditionally. For objects whose key carries their meaning.
    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError>;

    /// Remove the object. Removing what is not there succeeds.
    async fn delete(&self, key: &str) -> Result<(), StoreError>;

    /// The `max_keys` smallest keys under `prefix`, ascending.
    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError>;

    /// The sub-prefixes directly under `prefix`, up to the next `/`, ascending:
    /// a delimiter listing. Each ends with `/`.
    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError>;

    /// Whether the store answers.
    async fn ready(&self) -> bool;
}

/// One call the core asked for, made on `store`, as the core wants it
/// answered.
pub async fn call(store: &dyn Store, c: StoreCall) -> StoreOutcome {
    match c {
        StoreCall::Get { key } => match store.get(&key).await {
            Ok(r) => StoreOutcome::Got(r),
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::GetIfNoneMatch { key, etag } => match store.get_if_none_match(&key, &etag).await {
            Ok(r) => StoreOutcome::Read(r),
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::PutIfMatch { key, body, etag } => match store.put_if_match(&key, body, &etag).await {
            Ok(e) => StoreOutcome::Written(e),
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::PutIfNoneMatch { key, body } => match store.put_if_none_match(&key, body).await {
            Ok(e) => StoreOutcome::Written(e),
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::AppendIfMatch { key, offset, body, etag } => match store.append_if_match(&key, offset, body, &etag).await {
            Ok(e) => StoreOutcome::Written(e),
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::Put { key, body } => match store.put(&key, body).await {
            Ok(()) => StoreOutcome::Done,
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::Delete { key } => match store.delete(&key).await {
            Ok(()) => StoreOutcome::Done,
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::List { prefix, max_keys } => match store.list(&prefix, max_keys).await {
            Ok(r) => StoreOutcome::Listed(r),
            Err(e) => StoreOutcome::Failed(e),
        },
        StoreCall::ListPrefixes { prefix } => match store.list_prefixes(&prefix).await {
            Ok(r) => StoreOutcome::Listed(r),
            Err(e) => StoreOutcome::Failed(e),
        },
    }
}

// ---------------------------------------------------------------------------
// In memory
// ---------------------------------------------------------------------------

/// An in-process store with the same conditional semantics. Tests, and a
/// server with no bucket named.
pub struct MemoryStore {
    raw: Mutex<RawStore>,
    appendable: bool,
    listings: std::sync::atomic::AtomicUsize,
}

impl Default for MemoryStore {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryStore {
    pub fn new() -> Self {
        Self { raw: Mutex::new(RawStore::new("memory".into())), appendable: false, listings: Default::default() }
    }

    /// A store that appends, the way a directory bucket does.
    pub fn appendable() -> Self {
        Self { raw: Mutex::new(RawStore::new("memory".into())), appendable: true, listings: Default::default() }
    }

    /// How many listings have been asked of this store, for tests.
    pub fn listings(&self) -> usize {
        self.listings.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, RawStore> {
        self.raw.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn operation(call: StoreCall) -> Operation {
        fn key(value: String) -> Key {
            Key::new(value.into_bytes())
        }
        fn version(etag: Etag) -> u64 {
            // Raw versions start at one, so zero is stale for every malformed
            // or foreign ETag.
            etag.0.parse().unwrap_or(0)
        }
        match call {
            StoreCall::Get { key: value } => Operation::Get { key: key(value) },
            StoreCall::GetIfNoneMatch { key: value, etag } => Operation::GetIfNoneMatch { key: key(value), version: version(etag) },
            StoreCall::PutIfMatch { key: value, body, etag } => Operation::Update { key: key(value), version: version(etag), bytes: body },
            StoreCall::PutIfNoneMatch { key: value, body } => Operation::Create { key: key(value), bytes: body },
            StoreCall::AppendIfMatch { key: value, offset, body, etag } => Operation::Append { key: key(value), version: version(etag), offset, bytes: body },
            StoreCall::Put { key: value, body } => Operation::Put { key: key(value), bytes: body },
            StoreCall::Delete { key: value } => Operation::Delete { key: key(value) },
            StoreCall::List { prefix, max_keys } => Operation::List { prefix: key(prefix), max_keys },
            StoreCall::ListPrefixes { prefix } => Operation::ListPrefixes { prefix: key(prefix) },
        }
    }

    fn outcome(response: Response, environment: Environment) -> StoreOutcome {
        fn etag(version: u64) -> Etag {
            Etag(version.to_string())
        }
        fn key(value: Key) -> String {
            String::from_utf8(value.bytes).expect("runtime-created raw keys remain UTF-8")
        }
        match response {
            Response::Got(object) => StoreOutcome::Got(object.map(|object| (object.bytes, etag(object.version)))),
            Response::Read(RawRead::Body(object)) => StoreOutcome::Read(Read::Body(object.bytes, etag(object.version))),
            Response::Read(RawRead::NotModified) => StoreOutcome::Read(Read::NotModified),
            Response::Read(RawRead::Absent) => StoreOutcome::Read(Read::Absent),
            Response::Written(version) => StoreOutcome::Written(etag(version)),
            Response::Done => StoreOutcome::Done,
            Response::Listed(keys) => StoreOutcome::Listed(keys.into_iter().map(key).collect()),
            Response::Failed(Failure::Refused) => StoreOutcome::Failed(StoreError::PreconditionFailed),
            Response::Failed(Failure::Unavailable) => {
                let message = match environment {
                    Environment::ApplyButLostAck => "raw store applied the operation but lost its acknowledgement",
                    _ => "raw store unavailable before applying the operation",
                };
                StoreOutcome::Failed(StoreError::Unavailable(message.into()))
            }
            Response::InvalidChoice => StoreOutcome::Failed(StoreError::Unavailable("invalid environment choice for raw store operation".into())),
        }
    }

    /// Execute exactly one verified raw-store step with an explicit
    /// environmental disposition.
    pub fn execute_with_environment(&self, call: StoreCall, environment: Environment) -> StoreOutcome {
        self.execute_selecting_environment(call, |_, _| environment).1
    }

    /// Select an environment while the raw state is locked, then execute one
    /// step. The booleans say whether `Refused` and `ApplyButLostAck` are
    /// valid, respectively, for the operation and current state.
    pub fn execute_selecting_environment<F>(&self, call: StoreCall, select: F) -> (Environment, StoreOutcome)
    where
        F: FnOnce(bool, bool) -> Environment,
    {
        let listing = matches!(&call, StoreCall::List { .. } | StoreCall::ListPrefixes { .. });
        let operation = Self::operation(call);
        let mut raw = self.lock();
        let can_refuse = raw.accepts_environment(&operation, Environment::Refused);
        let can_lose_ack = raw.accepts_environment(&operation, Environment::ApplyButLostAck);
        let environment = select(can_refuse, can_lose_ack);
        if listing && environment != Environment::FailBeforeApply {
            self.listings.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        let response = raw.execute(operation, environment);
        (environment, Self::outcome(response, environment))
    }

    fn unexpected(expected: &str) -> StoreError {
        StoreError::Unavailable(format!("raw store returned an outcome other than {expected}"))
    }

    /// Every key, for tests.
    pub fn keys(&self) -> Vec<String> {
        let mut keys: Vec<String> = self.lock().entries.iter().map(|entry| {
            String::from_utf8(entry.key.bytes.clone()).expect("runtime-created raw keys remain UTF-8")
        }).collect();
        keys.sort();
        keys
    }
}

#[async_trait]
impl Store for MemoryStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        match self.execute_with_environment(StoreCall::Get { key: key.into() }, Environment::Normal) {
            StoreOutcome::Got(value) => Ok(value),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("Get")),
        }
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        match self.execute_with_environment(StoreCall::GetIfNoneMatch { key: key.into(), etag: etag.clone() }, Environment::Normal) {
            StoreOutcome::Read(value) => Ok(value),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("GetIfNoneMatch")),
        }
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        match self.execute_with_environment(StoreCall::PutIfMatch { key: key.into(), body, etag: etag.clone() }, Environment::Normal) {
            StoreOutcome::Written(etag) => Ok(etag),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("PutIfMatch")),
        }
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        match self.execute_with_environment(StoreCall::PutIfNoneMatch { key: key.into(), body }, Environment::Normal) {
            StoreOutcome::Written(etag) => Ok(etag),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("PutIfNoneMatch")),
        }
    }

    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        if !self.appendable {
            return Err(StoreError::Unavailable("this store does not append".into()));
        }
        match self.execute_with_environment(StoreCall::AppendIfMatch { key: key.into(), offset, body, etag: etag.clone() }, Environment::Normal) {
            StoreOutcome::Written(etag) => Ok(etag),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("AppendIfMatch")),
        }
    }

    fn supports_append(&self) -> bool {
        self.appendable
    }

    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        match self.execute_with_environment(StoreCall::Put { key: key.into(), body }, Environment::Normal) {
            StoreOutcome::Done => Ok(()),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("Put")),
        }
    }

    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        match self.execute_with_environment(StoreCall::Delete { key: key.into() }, Environment::Normal) {
            StoreOutcome::Done => Ok(()),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("Delete")),
        }
    }

    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        match self.execute_with_environment(StoreCall::List { prefix: prefix.into(), max_keys }, Environment::Normal) {
            StoreOutcome::Listed(keys) => Ok(keys),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("List")),
        }
    }

    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        match self.execute_with_environment(StoreCall::ListPrefixes { prefix: prefix.into() }, Environment::Normal) {
            StoreOutcome::Listed(prefixes) => Ok(prefixes),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("ListPrefixes")),
        }
    }

    async fn ready(&self) -> bool {
        true
    }
}

// ---------------------------------------------------------------------------
// S3
// ---------------------------------------------------------------------------

/// A bucket, through the AWS SDK. `express` is a directory bucket, which
/// appends.
pub struct S3Store {
    client: aws_sdk_s3::Client,
    bucket: String,
    express: bool,
}

impl S3Store {
    pub async fn open(bucket: &str, region: Option<&str>, endpoint: Option<&str>, express: bool) -> Self {
        let mut loader = aws_config::defaults(aws_config::BehaviorVersion::latest());
        if let Some(r) = region {
            loader = loader.region(aws_config::Region::new(r.to_string()));
        }
        if let Some(e) = endpoint {
            loader = loader.endpoint_url(e);
        }
        let shared = loader.load().await;
        let mut b = aws_sdk_s3::config::Builder::from(&shared);
        if endpoint.is_some() {
            b = b.force_path_style(true);
        }
        let client = aws_sdk_s3::Client::from_conf(b.build());
        Self { client, bucket: bucket.to_string(), express }
    }

    fn unavailable<E: std::fmt::Debug>(e: E) -> StoreError {
        StoreError::Unavailable(format!("{e:?}"))
    }

    fn strip(etag: Option<String>) -> Etag {
        Etag(etag.unwrap_or_default().trim_matches('"').to_string())
    }
}

fn status_of<E, R>(e: &aws_sdk_s3::error::SdkError<E, R>) -> Option<u16>
where
    R: aws_smithy_runtime_api_status::HasStatus,
{
    e.raw_response().map(|r| r.status())
}

/// A small shim so `status_of` can name the response's status without
/// pinning the SDK's http type in a signature.
mod aws_smithy_runtime_api_status {
    pub trait HasStatus {
        fn status(&self) -> u16;
    }
    impl HasStatus for aws_sdk_s3::config::http::HttpResponse {
        fn status(&self) -> u16 {
            self.status().as_u16()
        }
    }
}

#[async_trait]
impl Store for S3Store {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        match self.client.get_object().bucket(&self.bucket).key(key).send().await {
            Ok(out) => {
                let etag = Self::strip(out.e_tag().map(str::to_string));
                let bytes = out.body.collect().await.map_err(Self::unavailable)?.into_bytes().to_vec();
                Ok(Some((bytes, etag)))
            }
            Err(e) => {
                if matches!(status_of(&e), Some(404)) || e.as_service_error().map(|s| s.is_no_such_key()).unwrap_or(false) {
                    Ok(None)
                } else {
                    Err(Self::unavailable(e))
                }
            }
        }
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        match self.client.get_object().bucket(&self.bucket).key(key).if_none_match(format!("\"{}\"", etag.0)).send().await {
            Ok(out) => {
                let etag = Self::strip(out.e_tag().map(str::to_string));
                let bytes = out.body.collect().await.map_err(Self::unavailable)?.into_bytes().to_vec();
                Ok(Read::Body(bytes, etag))
            }
            Err(e) => match status_of(&e) {
                Some(304) => Ok(Read::NotModified),
                Some(404) => Ok(Read::Absent),
                _ if e.as_service_error().map(|s| s.is_no_such_key()).unwrap_or(false) => Ok(Read::Absent),
                _ => Err(Self::unavailable(e)),
            },
        }
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        match self.client.put_object().bucket(&self.bucket).key(key).if_match(format!("\"{}\"", etag.0)).body(body.into()).send().await {
            Ok(out) => Ok(Self::strip(out.e_tag().map(str::to_string))),
            Err(e) => match status_of(&e) {
                Some(412) | Some(409) => Err(StoreError::PreconditionFailed),
                _ => Err(Self::unavailable(e)),
            },
        }
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        match self.client.put_object().bucket(&self.bucket).key(key).if_none_match("*").body(body.into()).send().await {
            Ok(out) => Ok(Self::strip(out.e_tag().map(str::to_string))),
            Err(e) => match status_of(&e) {
                Some(412) | Some(409) => Err(StoreError::PreconditionFailed),
                _ => Err(Self::unavailable(e)),
            },
        }
    }

    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        if !self.express {
            return Err(StoreError::Unavailable("this bucket does not append".into()));
        }
        match self
            .client
            .put_object()
            .bucket(&self.bucket)
            .key(key)
            .if_match(format!("\"{}\"", etag.0))
            .write_offset_bytes(offset as i64)
            .body(body.into())
            .send()
            .await
        {
            Ok(out) => Ok(Self::strip(out.e_tag().map(str::to_string))),
            Err(e) => match status_of(&e) {
                Some(412) | Some(409) | Some(400) => Err(StoreError::PreconditionFailed),
                _ => Err(Self::unavailable(e)),
            },
        }
    }

    fn supports_append(&self) -> bool {
        self.express
    }

    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        self.client.put_object().bucket(&self.bucket).key(key).body(body.into()).send().await.map(|_| ()).map_err(Self::unavailable)
    }

    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        self.client.delete_object().bucket(&self.bucket).key(key).send().await.map(|_| ()).map_err(Self::unavailable)
    }

    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        let mut keys = Vec::new();
        let mut token: Option<String> = None;
        loop {
            let mut req = self.client.list_objects_v2().bucket(&self.bucket).prefix(prefix).max_keys((max_keys - keys.len()).min(1000) as i32);
            if let Some(t) = &token {
                req = req.continuation_token(t);
            }
            let out = req.send().await.map_err(Self::unavailable)?;
            for o in out.contents() {
                if let Some(k) = o.key() {
                    keys.push(k.to_string());
                }
            }
            if keys.len() >= max_keys {
                keys.truncate(max_keys);
                break;
            }
            match out.next_continuation_token() {
                Some(t) if out.is_truncated().unwrap_or(false) => token = Some(t.to_string()),
                _ => break,
            }
        }
        // General-purpose buckets list in order; directory buckets do not.
        keys.sort();
        Ok(keys)
    }

    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        let mut out = Vec::new();
        let mut token: Option<String> = None;
        loop {
            let mut req = self.client.list_objects_v2().bucket(&self.bucket).prefix(prefix).delimiter("/").max_keys(1000);
            if let Some(t) = &token {
                req = req.continuation_token(t);
            }
            let resp = req.send().await.map_err(Self::unavailable)?;
            for p in resp.common_prefixes() {
                if let Some(p) = p.prefix() {
                    out.push(p.to_string());
                }
            }
            match resp.next_continuation_token() {
                Some(t) if resp.is_truncated().unwrap_or(false) => token = Some(t.to_string()),
                _ => break,
            }
        }
        out.sort();
        Ok(out)
    }

    async fn ready(&self) -> bool {
        self.client.head_bucket().bucket(&self.bucket).send().await.is_ok()
    }
}

// ---------------------------------------------------------------------------
// Any object store, through `object_store`
// ---------------------------------------------------------------------------

/// The `object_store` crate behind the port: S3, GCS, Azure, the local
/// filesystem and memory, each with conditional writes of its own. Versions
/// are the store's ETags as it gives them, quotes included: they are only
/// ever handed back to the same store.
use object_store::ObjectStoreExt as _;

pub struct ObjectStoreStore {
    inner: Arc<dyn object_store::ObjectStore>,
    /// The path inside the store every key lives under.
    root: object_store::path::Path,
}

impl ObjectStoreStore {
    pub fn new(inner: Arc<dyn object_store::ObjectStore>, root: object_store::path::Path) -> Self {
        Self { inner, root }
    }

    /// A store named by a URL: `s3://bucket/prefix`, `gs://bucket`,
    /// `az://container`, `file:///dir`, `memory:///`. For S3, `endpoint` and
    /// `region` override what the environment says; credentials come from
    /// the environment.
    pub fn from_url(url: &str, endpoint: Option<&str>, region: Option<&str>) -> Result<Self, String> {
        let parsed = url::Url::parse(url).map_err(|e| format!("bad store url {url}: {e}"))?;
        let (inner, root): (Box<dyn object_store::ObjectStore>, object_store::path::Path) = match parsed.scheme() {
            "s3" | "s3a" => {
                let mut b = object_store::aws::AmazonS3Builder::from_env().with_url(url);
                if let Some(e) = endpoint {
                    b = b.with_endpoint(e).with_allow_http(e.starts_with("http://")).with_virtual_hosted_style_request(false);
                }
                if let Some(r) = region {
                    b = b.with_region(r);
                }
                let path = object_store::path::Path::parse(parsed.path()).map_err(|e| e.to_string())?;
                (Box::new(b.build().map_err(|e| e.to_string())?), path)
            }
            _ => object_store::parse_url(&parsed).map_err(|e| e.to_string())?,
        };
        Ok(Self { inner: Arc::from(inner), root })
    }

    fn path(&self, key: &str) -> Result<object_store::path::Path, StoreError> {
        let p = object_store::path::Path::parse(key).map_err(|e| StoreError::Unavailable(format!("bad key {key}: {e}")))?;
        if self.root.as_ref().is_empty() {
            Ok(p)
        } else {
            Ok(object_store::path::Path::from_iter(self.root.parts().chain(p.parts())))
        }
    }

    fn key(&self, p: &object_store::path::Path) -> String {
        let s = p.as_ref();
        if self.root.as_ref().is_empty() {
            s.to_string()
        } else {
            s.strip_prefix(self.root.as_ref()).map(|r| r.trim_start_matches('/')).unwrap_or(s).to_string()
        }
    }

    fn etag(e: Option<String>) -> Result<Etag, StoreError> {
        e.map(Etag).ok_or_else(|| StoreError::Unavailable("the store gives no version".into()))
    }

    fn unavailable(e: object_store::Error) -> StoreError {
        StoreError::Unavailable(e.to_string())
    }
}

#[async_trait]
impl Store for ObjectStoreStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        let p = self.path(key)?;
        match self.inner.get(&p).await {
            Ok(r) => {
                let etag = Self::etag(r.meta.e_tag.clone())?;
                let bytes = r.bytes().await.map_err(Self::unavailable)?.to_vec();
                Ok(Some((bytes, etag)))
            }
            Err(object_store::Error::NotFound { .. }) => Ok(None),
            Err(e) => Err(Self::unavailable(e)),
        }
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        let p = self.path(key)?;
        let opts = object_store::GetOptions { if_none_match: Some(etag.0.clone()), ..Default::default() };
        match self.inner.get_opts(&p, opts).await {
            Ok(r) => {
                let e = Self::etag(r.meta.e_tag.clone())?;
                if e == *etag {
                    // A store that ignores the condition and sends the body.
                    return Ok(Read::NotModified);
                }
                let bytes = r.bytes().await.map_err(Self::unavailable)?.to_vec();
                Ok(Read::Body(bytes, e))
            }
            Err(object_store::Error::NotModified { .. }) => Ok(Read::NotModified),
            Err(object_store::Error::NotFound { .. }) => Ok(Read::Absent),
            Err(e) => Err(Self::unavailable(e)),
        }
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        let p = self.path(key)?;
        let opts = object_store::PutOptions {
            mode: object_store::PutMode::Update(object_store::UpdateVersion { e_tag: Some(etag.0.clone()), version: None }),
            ..Default::default()
        };
        match self.inner.put_opts(&p, body.into(), opts).await {
            Ok(r) => Self::etag(r.e_tag),
            Err(object_store::Error::Precondition { .. }) | Err(object_store::Error::NotFound { .. }) | Err(object_store::Error::AlreadyExists { .. }) => Err(StoreError::PreconditionFailed),
            Err(e) => Err(Self::unavailable(e)),
        }
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        let p = self.path(key)?;
        let opts = object_store::PutOptions { mode: object_store::PutMode::Create, ..Default::default() };
        match self.inner.put_opts(&p, body.into(), opts).await {
            Ok(r) => Self::etag(r.e_tag),
            Err(object_store::Error::AlreadyExists { .. }) | Err(object_store::Error::Precondition { .. }) => Err(StoreError::PreconditionFailed),
            Err(e) => Err(Self::unavailable(e)),
        }
    }

    async fn append_if_match(&self, _key: &str, _offset: u64, _body: Vec<u8>, _etag: &Etag) -> Result<Etag, StoreError> {
        Err(StoreError::Unavailable("this store does not append".into()))
    }

    fn supports_append(&self) -> bool {
        false
    }

    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        let p = self.path(key)?;
        self.inner.put(&p, body.into()).await.map(|_| ()).map_err(Self::unavailable)
    }

    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        let p = self.path(key)?;
        match self.inner.delete(&p).await {
            Ok(()) | Err(object_store::Error::NotFound { .. }) => Ok(()),
            Err(e) => Err(Self::unavailable(e)),
        }
    }

    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        use futures::TryStreamExt;
        let p = self.path(prefix)?;
        let under = if prefix.is_empty() && self.root.as_ref().is_empty() { None } else { Some(&p) };
        let metas: Vec<object_store::ObjectMeta> = self.inner.list(under).try_collect().await.map_err(Self::unavailable)?;
        let mut keys: Vec<String> = metas.iter().map(|m| self.key(&m.location)).collect();
        keys.sort();
        keys.truncate(max_keys);
        Ok(keys)
    }

    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        let p = self.path(prefix)?;
        let under = if prefix.is_empty() && self.root.as_ref().is_empty() { None } else { Some(&p) };
        let r = self.inner.list_with_delimiter(under).await.map_err(Self::unavailable)?;
        let mut out: Vec<String> = r.common_prefixes.iter().map(|c| format!("{}/", self.key(c))).collect();
        out.sort();
        Ok(out)
    }

    async fn ready(&self) -> bool {
        let under = if self.root.as_ref().is_empty() { None } else { Some(&self.root) };
        self.inner.list_with_delimiter(under).await.is_ok()
    }
}

/// The store a configuration names.
pub async fn open(cfg: &crate::Config) -> Result<Arc<dyn Store>, String> {
    if let Some(url) = &cfg.store {
        tracing::info!(store = %url, prefix = %cfg.prefix, "using an object store");
        return Ok(Arc::new(ObjectStoreStore::from_url(url, cfg.endpoint.as_deref(), cfg.region.as_deref())?));
    }
    match &cfg.bucket {
        None => {
            tracing::warn!("no store named: using an in-memory store, nothing survives this process");
            Ok(Arc::new(MemoryStore::new()))
        }
        Some(bucket) if cfg.express => {
            tracing::info!(bucket = %bucket, prefix = %cfg.prefix, "using an S3 directory bucket, appending");
            Ok(Arc::new(S3Store::open(bucket, cfg.region.as_deref(), cfg.endpoint.as_deref(), true).await))
        }
        Some(bucket) => {
            tracing::info!(bucket = %bucket, prefix = %cfg.prefix, "using S3");
            Ok(Arc::new(ObjectStoreStore::from_url(&format!("s3://{bucket}"), cfg.endpoint.as_deref(), cfg.region.as_deref())?))
        }
    }
}

