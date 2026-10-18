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

    fn etag(v: u64) -> Etag {
        Etag(format!("v{v}"))
    }

    /// Every key, for tests.
    pub fn keys(&self) -> Vec<String> {
        self.lock().keys().cloned().collect()
    }
}

#[async_trait]
impl Store for MemoryStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        Ok(self.lock().get(key).map(|(b, v)| (b.clone(), Self::etag(*v))))
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        Ok(match self.lock().get(key) {
            None => Read::Absent,
            Some((_, v)) if Self::etag(*v) == *etag => Read::NotModified,
            Some((b, v)) => Read::Body(b.clone(), Self::etag(*v)),
        })
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        let mut m = self.lock();
        match m.get(key) {
            Some((_, v)) if Self::etag(*v) == *etag => {
                let nv = v + 1;
                m.insert(key.to_string(), (body, nv));
                Ok(Self::etag(nv))
            }
            _ => Err(StoreError::PreconditionFailed),
        }
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        let mut m = self.lock();
        if m.contains_key(key) {
            return Err(StoreError::PreconditionFailed);
        }
        m.insert(key.to_string(), (body, 1));
        Ok(Self::etag(1))
    }

    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        if !self.appendable {
            return Err(StoreError::Unavailable("this store does not append".into()));
        }
        let mut m = self.lock();
        match m.get_mut(key) {
            Some((b, v)) if Self::etag(*v) == *etag && b.len() as u64 == offset => {
                b.extend_from_slice(&body);
                *v += 1;
                Ok(Self::etag(*v))
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

/// The store a configuration names.
pub async fn open(cfg: &crate::Config) -> Arc<dyn Store> {
    match &cfg.bucket {
        None => {
            tracing::warn!("no bucket named: using an in-memory store, nothing survives this process");
            Arc::new(MemoryStore::new())
        }
        Some(bucket) => {
            tracing::info!(bucket = %bucket, prefix = %cfg.prefix, express = cfg.express, "using S3");
            Arc::new(S3Store::open(bucket, cfg.region.as_deref(), cfg.endpoint.as_deref(), cfg.express).await)
        }
    }
}

/// A store failure as the port's one error.
pub fn unavailable_err(e: StoreError) -> resonate_core::Unavailable {
    resonate_core::Unavailable::new(e.to_string())
}
