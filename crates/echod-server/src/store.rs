//! The object store port.
//!
//! Every write that commits state is conditional on the version the writer
//! read: `If-Match` on the ETag, or `If-None-Match: *` for a fresh key. A
//! directory bucket also appends; a general-purpose bucket rewrites. Timer and
//! node objects carry their meaning in the key and are written blind.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use async_trait::async_trait;

/// An object's version, as the store reports it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Etag(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StoreError {
    /// Someone else wrote first. Re-read, re-decide, never replay.
    PreconditionFailed,
    /// No answer at all.
    Unavailable(String),
}

impl std::fmt::Display for StoreError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StoreError::PreconditionFailed => f.write_str("precondition failed"),
            StoreError::Unavailable(m) => write!(f, "store unavailable: {m}"),
        }
    }
}

impl std::error::Error for StoreError {}

/// What a read returned.
#[derive(Debug, Clone)]
pub enum Read {
    /// The object, its version, and its size in bytes.
    Body(Vec<u8>, Etag),
    /// Still the version the caller held.
    NotModified,
    Absent,
}

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

// ---------------------------------------------------------------------------
// In memory
// ---------------------------------------------------------------------------

/// An in-process store with the same conditional semantics. Tests, and a
/// server with no bucket named.
#[derive(Default)]
pub struct MemoryStore {
    objects: Mutex<BTreeMap<String, (Vec<u8>, u64)>>,
    appendable: bool,
    listings: std::sync::atomic::AtomicUsize,
}

impl MemoryStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// A store that appends, the way a directory bucket does.
    pub fn appendable() -> Self {
        Self { objects: Mutex::new(BTreeMap::new()), appendable: true, listings: Default::default() }
    }

    /// How many listings have been asked of this store, for tests.
    pub fn listings(&self) -> usize {
        self.listings.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, BTreeMap<String, (Vec<u8>, u64)>> {
        self.objects.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// The version is the content, as an S3 ETag is: writing the same bytes
    /// again yields the same version. A writer that must move the version
    /// changes the bytes.
    fn etag(body: &[u8]) -> Etag {
        Etag(format!("{:016x}", crate::keys::fnv1a(&String::from_utf8_lossy(body))))
    }

    /// Every key, for tests.
    pub fn keys(&self) -> Vec<String> {
        self.lock().keys().cloned().collect()
    }
}

#[async_trait]
impl Store for MemoryStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        Ok(self.lock().get(key).map(|(b, _)| (b.clone(), Self::etag(b))))
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        Ok(match self.lock().get(key) {
            None => Read::Absent,
            Some((b, _)) if Self::etag(b) == *etag => Read::NotModified,
            Some((b, _)) => Read::Body(b.clone(), Self::etag(b)),
        })
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        let mut m = self.lock();
        match m.get(key) {
            Some((b, v)) if Self::etag(b) == *etag => {
                let nv = v + 1;
                let e = Self::etag(&body);
                m.insert(key.to_string(), (body, nv));
                Ok(e)
            }
            _ => Err(StoreError::PreconditionFailed),
        }
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        let mut m = self.lock();
        if m.contains_key(key) {
            return Err(StoreError::PreconditionFailed);
        }
        let e = Self::etag(&body);
        m.insert(key.to_string(), (body, 1));
        Ok(e)
    }

    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        if !self.appendable {
            return Err(StoreError::Unavailable("this store does not append".into()));
        }
        let mut m = self.lock();
        match m.get_mut(key) {
            Some((b, v)) if Self::etag(b) == *etag && b.len() as u64 == offset => {
                b.extend_from_slice(&body);
                *v += 1;
                Ok(Self::etag(b))
            }
            _ => Err(StoreError::PreconditionFailed),
        }
    }

    fn supports_append(&self) -> bool {
        self.appendable
    }

    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        let mut m = self.lock();
        let v = m.get(key).map(|(_, v)| v + 1).unwrap_or(1);
        m.insert(key.to_string(), (body, v));
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        self.lock().remove(key);
        Ok(())
    }

    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        self.listings.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(self.lock().range(prefix.to_string()..).take_while(|(k, _)| k.starts_with(prefix)).take(max_keys).map(|(k, _)| k.clone()).collect())
    }

    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        self.listings.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let mut out: Vec<String> = Vec::new();
        for (k, _) in self.lock().range(prefix.to_string()..).take_while(|(k, _)| k.starts_with(prefix)) {
            if let Some(i) = k[prefix.len()..].find('/') {
                let p = k[..prefix.len() + i + 1].to_string();
                if out.last() != Some(&p) {
                    out.push(p);
                }
            }
        }
        Ok(out)
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

/// A store failure as the port's one error.
pub fn unavailable_err(e: StoreError) -> resonate_core::Unavailable {
    resonate_core::Unavailable::new(e.to_string())
}
