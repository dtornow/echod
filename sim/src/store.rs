//! An in-memory S3 that misbehaves on request.
//!
//! Every operation waits a virtual latency first, which is what makes two
//! requests overlap at all. On top of that, by percentages drawn from the
//! seed: an operation answers nothing (`unavailable`); a write lands and is
//! reported as failed (`lost_ack`); a conditional write is refused although
//! nothing moved (`conflict`). Each is a case the real service produces, and
//! each has a repair the node must get right.

use std::sync::{Arc, Mutex};
use std::time::Duration;

use async_trait::async_trait;
use echod::store::{Environment, Etag, MemoryStore, Read, Store, StoreCall, StoreError, StoreOutcome};

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

    fn increment(&self, counter: fn(&mut Counters) -> &mut u64) {
        *counter(&mut self.counters.lock().unwrap()) += 1;
    }

    async fn execute(&self, call: StoreCall) -> StoreOutcome {
        self.delay().await;
        let conditional = matches!(&call, StoreCall::PutIfMatch { .. } | StoreCall::PutIfNoneMatch { .. } | StoreCall::AppendIfMatch { .. });
        let mutation = matches!(&call, StoreCall::PutIfMatch { .. } | StoreCall::PutIfNoneMatch { .. } | StoreCall::AppendIfMatch { .. } | StoreCall::Put { .. } | StoreCall::Delete { .. });
        self.inner.execute_selecting_environment(call, |can_refuse, can_lose_ack| {
            if self.roll(self.faults.unavailable_percent) {
                self.increment(|c| &mut c.unavailable);
                return Environment::FailBeforeApply;
            }
            // Draw for every conditional request, but select Refused only
            // when that is a valid raw transition in the locked state.
            if conditional && self.roll(self.faults.conflict_percent) && can_refuse {
                self.increment(|c| &mut c.conflicts);
                return Environment::Refused;
            }
            // Eligibility is known before the one automaton step.
            if mutation && can_lose_ack && self.roll(self.faults.lost_ack_percent) {
                self.increment(|c| &mut c.lost_acks);
                return Environment::ApplyButLostAck;
            }
            Environment::Normal
        }).1
    }

    fn unexpected(expected: &str) -> StoreError {
        StoreError::Unavailable(format!("raw store returned an outcome other than {expected}"))
    }
}

#[async_trait]
impl Store for FaultyStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        match self.execute(StoreCall::Get { key: key.into() }).await {
            StoreOutcome::Got(value) => Ok(value),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("Get")),
        }
    }

    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        match self.execute(StoreCall::GetIfNoneMatch { key: key.into(), etag: etag.clone() }).await {
            StoreOutcome::Read(value) => Ok(value),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("GetIfNoneMatch")),
        }
    }

    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        match self.execute(StoreCall::PutIfMatch { key: key.into(), body, etag: etag.clone() }).await {
            StoreOutcome::Written(etag) => Ok(etag),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("PutIfMatch")),
        }
    }

    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        match self.execute(StoreCall::PutIfNoneMatch { key: key.into(), body }).await {
            StoreOutcome::Written(etag) => Ok(etag),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("PutIfNoneMatch")),
        }
    }

    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        if !self.inner.supports_append() {
            self.delay().await;
            if self.roll(self.faults.unavailable_percent) {
                self.increment(|c| &mut c.unavailable);
                return Err(StoreError::Unavailable("injected".into()));
            }
            if self.roll(self.faults.conflict_percent) {
                self.increment(|c| &mut c.conflicts);
                return Err(StoreError::PreconditionFailed);
            }
            return Err(StoreError::Unavailable("this store does not append".into()));
        }
        match self.execute(StoreCall::AppendIfMatch { key: key.into(), offset, body, etag: etag.clone() }).await {
            StoreOutcome::Written(etag) => Ok(etag),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("AppendIfMatch")),
        }
    }

    fn supports_append(&self) -> bool {
        self.inner.supports_append()
    }

    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        match self.execute(StoreCall::Put { key: key.into(), body }).await {
            StoreOutcome::Done => Ok(()),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("Put")),
        }
    }

    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        match self.execute(StoreCall::Delete { key: key.into() }).await {
            StoreOutcome::Done => Ok(()),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("Delete")),
        }
    }

    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        match self.execute(StoreCall::List { prefix: prefix.into(), max_keys }).await {
            StoreOutcome::Listed(keys) => Ok(keys),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("List")),
        }
    }

    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        match self.execute(StoreCall::ListPrefixes { prefix: prefix.into() }).await {
            StoreOutcome::Listed(prefixes) => Ok(prefixes),
            StoreOutcome::Failed(error) => Err(error),
            _ => Err(Self::unexpected("ListPrefixes")),
        }
    }

    async fn ready(&self) -> bool {
        true
    }
}

/// One node's view of the store: the shared faulty store, or nothing at all
/// while the node is cut off from it.
pub struct NodeStore {
    pub shared: Arc<FaultyStore>,
    cut: std::sync::atomic::AtomicBool,
}

impl NodeStore {
    pub fn new(shared: Arc<FaultyStore>) -> Self {
        Self { shared, cut: std::sync::atomic::AtomicBool::new(false) }
    }

    pub fn set_cut(&self, cut: bool) {
        self.cut.store(cut, std::sync::atomic::Ordering::Relaxed);
    }

    async fn gate(&self) -> Result<(), StoreError> {
        if self.cut.load(std::sync::atomic::Ordering::Relaxed) {
            tokio::task::yield_now().await;
            return Err(StoreError::Unavailable("this node cannot reach the store".into()));
        }
        Ok(())
    }
}

#[async_trait]
impl Store for NodeStore {
    async fn get(&self, key: &str) -> Result<Option<(Vec<u8>, Etag)>, StoreError> {
        self.gate().await?;
        self.shared.get(key).await
    }
    async fn get_if_none_match(&self, key: &str, etag: &Etag) -> Result<Read, StoreError> {
        self.gate().await?;
        self.shared.get_if_none_match(key, etag).await
    }
    async fn put_if_match(&self, key: &str, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        self.gate().await?;
        self.shared.put_if_match(key, body, etag).await
    }
    async fn put_if_none_match(&self, key: &str, body: Vec<u8>) -> Result<Etag, StoreError> {
        self.gate().await?;
        self.shared.put_if_none_match(key, body).await
    }
    async fn append_if_match(&self, key: &str, offset: u64, body: Vec<u8>, etag: &Etag) -> Result<Etag, StoreError> {
        self.gate().await?;
        self.shared.append_if_match(key, offset, body, etag).await
    }
    fn supports_append(&self) -> bool {
        self.shared.supports_append()
    }
    async fn put(&self, key: &str, body: Vec<u8>) -> Result<(), StoreError> {
        self.gate().await?;
        self.shared.put(key, body).await
    }
    async fn delete(&self, key: &str) -> Result<(), StoreError> {
        self.gate().await?;
        self.shared.delete(key).await
    }
    async fn list(&self, prefix: &str, max_keys: usize) -> Result<Vec<String>, StoreError> {
        self.gate().await?;
        self.shared.list(prefix, max_keys).await
    }
    async fn list_prefixes(&self, prefix: &str) -> Result<Vec<String>, StoreError> {
        self.gate().await?;
        self.shared.list_prefixes(prefix).await
    }
    async fn ready(&self) -> bool {
        !self.cut.load(std::sync::atomic::Ordering::Relaxed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn faulty(inner: Arc<MemoryStore>, faults: Faults) -> FaultyStore {
        FaultyStore::new(inner, faults, Rng::new(1))
    }

    #[tokio::test]
    async fn unavailable_is_selected_before_the_raw_step() {
        let inner = Arc::new(MemoryStore::new());
        let store = faulty(Arc::clone(&inner), Faults { unavailable_percent: 100, ..Faults::default() });

        assert!(matches!(store.put("k", b"value".to_vec()).await, Err(StoreError::Unavailable(_))));
        assert_eq!(inner.get("k").await.unwrap(), None);
        assert_eq!(store.counters().operations, 1);
        assert_eq!(store.counters().unavailable, 1);
    }

    #[tokio::test]
    async fn lost_ack_is_an_apply_but_lost_ack_raw_step() {
        let inner = Arc::new(MemoryStore::new());
        let store = faulty(Arc::clone(&inner), Faults { lost_ack_percent: 100, ..Faults::default() });

        assert!(matches!(store.put("k", b"value".to_vec()).await, Err(StoreError::Unavailable(_))));
        assert_eq!(inner.get("k").await.unwrap().unwrap().0, b"value");
        assert_eq!(store.counters().operations, 1);
        assert_eq!(store.counters().lost_acks, 1);
    }

    #[tokio::test]
    async fn stale_conflict_is_a_refused_raw_step() {
        let inner = Arc::new(MemoryStore::new());
        let current = inner.put_if_none_match("k", b"value".to_vec()).await.unwrap();
        let store = faulty(Arc::clone(&inner), Faults { conflict_percent: 100, lost_ack_percent: 100, ..Faults::default() });

        assert_eq!(store.put_if_none_match("k", b"other".to_vec()).await, Err(StoreError::PreconditionFailed));
        assert_eq!(inner.get("k").await.unwrap(), Some((b"value".to_vec(), current)));
        assert_eq!(store.counters().operations, 1);
        assert_eq!(store.counters().conflicts, 1);
        assert_eq!(store.counters().lost_acks, 0);
    }
}
