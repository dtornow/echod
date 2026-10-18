//! An in-memory S3 that misbehaves on request.
//!
//! Every operation waits a virtual latency first, which is what makes two
//! requests overlap at all. On top of that, by percentages drawn from the
//! seed: an operation answers nothing (`unavailable`); a write lands and is
//! reported as failed (`lost_ack`); a conditional write is refused although
//! nothing moved (`conflict`). Each is a case the real service produces, and
//! each has a repair the server must get right.

use std::sync::{Arc, Mutex};
use std::time::Duration;

use async_trait::async_trait;
use echod_server::store::{Etag, MemoryStore, Read, Store, StoreError};

use crate::rng::Rng;

#[derive(Clone, Copy, Debug, Default)]
pub struct Faults {
    /// Per operation: no answer, nothing done.
    pub unavailable_percent: u64,
    /// Per write: done, and reported as not done.
    pub lost_ack_percent: u64,
    /// Per conditional write: refused with nothing moved.
    pub conflict_percent: u64,
    /// Each operation waits `0..=latency_ms` before it runs.
    pub latency_ms: u64,
}

#[derive(Debug, Default, Clone, Copy)]
pub struct Counters {
    pub operations: u64,
    pub unavailable: u64,
    pub lost_acks: u64,
    pub conflicts: u64,
}

pub struct FaultyStore {
    pub inner: Arc<MemoryStore>,
    faults: Faults,
    rng: Mutex<Rng>,
    counters: Mutex<Counters>,
}

impl FaultyStore {
    pub fn new(inner: Arc<MemoryStore>, faults: Faults, rng: Rng) -> Self {
        Self { inner, faults, rng: Mutex::new(rng), counters: Mutex::new(Counters::default()) }
    }

    pub fn counters(&self) -> Counters {
        *self.counters.lock().unwrap()
    }

    fn roll(&self, percent: u64) -> bool {
        self.rng.lock().unwrap().percent(percent)
    }

    async fn delay(&self) {
        self.counters.lock().unwrap().operations += 1;
        let ms = { self.rng.lock().unwrap().range(0, self.faults.latency_ms) };
        if ms > 0 {
            tokio::time::sleep(Duration::from_millis(ms)).await;
        } else {
            tokio::task::yield_now().await;
        }
    }

    fn unavailable(&self) -> Option<StoreError> {
        if self.roll(self.faults.unavailable_percent) {
            self.counters.lock().unwrap().unavailable += 1;
            Some(StoreError::Unavailable("injected".into()))
        } else {
            None
        }
    }

    /// After a write landed: maybe say it did not.
    fn lost_ack<T>(&self, r: Result<T, StoreError>) -> Result<T, StoreError> {
        if r.is_ok() && self.roll(self.faults.lost_ack_percent) {
            self.counters.lock().unwrap().lost_acks += 1;
            return Err(StoreError::Unavailable("injected: ack lost".into()));
        }
        r
    }

    fn conflict(&self) -> Option<StoreError> {
        if self.roll(self.faults.conflict_percent) {
            self.counters.lock().unwrap().conflicts += 1;
            Some(StoreError::PreconditionFailed)
        } else {
            None
        }
    }
}

#[async_trait]
impl Store for FaultyStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        self.inner.get(key).await
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        self.inner.get_if_none_match(key, etag).await
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        if let Some(e) = self.conflict() {
            return Err(e);
        }
        let r = self.inner.put_if_match(key, body, etag).await;
        self.lost_ack(r)
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        if let Some(e) = self.conflict() {
            return Err(e);
        }
        let r = self.inner.put_if_none_match(key, body).await;
        self.lost_ack(r)
    }

    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        if let Some(e) = self.conflict() {
            return Err(e);
        }
        let r = self.inner.append_if_match(key, offset, body, etag).await;
        self.lost_ack(r)
    }

    fn supports_append(&self) -> bool {
        self.inner.supports_append()
    }

    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        let r = self.inner.put(key, body).await;
        self.lost_ack(r)
    }

    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        let r = self.inner.delete(key).await;
        self.lost_ack(r)
    }

    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        self.inner.list(prefix, max_keys).await
    }

    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        self.delay().await;
        if let Some(e) = self.unavailable() {
            return Err(e);
        }
        self.inner.list_prefixes(prefix).await
    }

    async fn ready(&self) -> bool {
        true
    }
}
