//! The synchronous shared store and its seeded faults.
//!
//! A call is first planned, yielding a virtual completion delay and a fault
//! disposition. The event loop later completes it with the production
//! concrete store's verified `Store::apply` transition. There are no futures,
//! threads, locks, or I/O here.

use echod_logic::concrete::store::Store;
use echod_logic::types::{StoreReq, StoreError, StoreRes};

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

#[derive(Clone, Copy, Debug)]
pub enum Disposition {
    Apply,
    Unavailable,
    Conflict,
}

pub struct FaultyStore {
    pub inner: Store,
    faults: Faults,
    rng: Rng,
    counters: Counters,
}

impl FaultyStore {
    pub fn new(appendable: bool, faults: Faults, rng: Rng) -> Self {
        Self {
            inner: Store::empty(appendable),
            faults,
            rng,
            counters: Counters::default(),
        }
    }

    pub fn counters(&self) -> Counters {
        self.counters
    }

    /// Plan one reachable store operation. A node-local outage is handled by
    /// the event loop before this method and is not a shared-store operation.
    pub fn plan(&mut self, call: &StoreReq) -> (u64, Disposition) {
        self.counters.operations += 1;
        let delay = self.rng.range(0, self.faults.latency_ms);
        if self.rng.percent(self.faults.unavailable_percent) {
            self.counters.unavailable += 1;
            return (delay, Disposition::Unavailable);
        }
        if conditional(call) && self.rng.percent(self.faults.conflict_percent) {
            self.counters.conflicts += 1;
            return (delay, Disposition::Conflict);
        }
        (delay, Disposition::Apply)
    }

    /// Complete a planned operation. Lost acknowledgements happen only after
    /// a successful write has changed the shared store.
    pub fn complete(&mut self, call: &StoreReq, disposition: Disposition) -> StoreRes {
        match disposition {
            Disposition::Unavailable => {
                failure(call, StoreError::Unavailable("injected".into()))
            }
            Disposition::Conflict => failure(call, StoreError::PreconditionFailed),
            Disposition::Apply => {
                let (next, outcome) = self.inner.apply(call);
                self.inner = next;
                if write(call)
                    && response_error(&outcome).is_none()
                    && self.rng.percent(self.faults.lost_ack_percent)
                {
                    self.counters.lost_acks += 1;
                    failure(call, StoreError::Unavailable("injected: ack lost".into()))
                } else {
                    outcome
                }
            }
        }
    }

    pub fn get(&self, key: &str) -> Option<&[u8]> {
        self.inner
            .entries
            .iter()
            .find(|entry| entry.key == key)
            .map(|entry| entry.body.as_slice())
    }

    pub fn list(&self, prefix: &str) -> Vec<String> {
        self.inner
            .entries
            .iter()
            .filter(|entry| entry.key.starts_with(prefix))
            .map(|entry| entry.key.clone())
            .collect()
    }
}

fn conditional(call: &StoreReq) -> bool {
    matches!(
        call,
        StoreReq::PutIfMatch { .. }
            | StoreReq::PutIfNoneMatch { .. }
            | StoreReq::AppIfMatch { .. }
    )
}

fn write(call: &StoreReq) -> bool {
    matches!(
        call,
        StoreReq::PutIfMatch { .. }
            | StoreReq::PutIfNoneMatch { .. }
            | StoreReq::AppIfMatch { .. }
            | StoreReq::Put { .. }
            | StoreReq::Del { .. }
    )
}

fn failure(call: &StoreReq, error: StoreError) -> StoreRes {
match call {
StoreReq::Get { .. } => StoreRes::Get { result: Err(error) },
StoreReq::GetIfNoneMatch { .. } => StoreRes::GetIfNoneMatch { result: Err(error) },
StoreReq::PutIfMatch { .. } => StoreRes::PutIfMatch { result: Err(error) },
StoreReq::PutIfNoneMatch { .. } => StoreRes::PutIfNoneMatch { result: Err(error) },
StoreReq::AppIfMatch { .. } => StoreRes::AppIfMatch { result: Err(error) },
StoreReq::Put { .. } => StoreRes::Put { result: Err(error) },
StoreReq::Del { .. } => StoreRes::Del { result: Err(error) },
StoreReq::List { .. } => StoreRes::List { result: Err(error) },
StoreReq::ListPrefixes { .. } => StoreRes::ListPrefixes { result: Err(error) },
}
}

pub(crate) fn response_error(response: &StoreRes) -> Option<&StoreError> {
match response {
StoreRes::Get { result } => result.as_ref().err(),
StoreRes::GetIfNoneMatch { result } => result.as_ref().err(),
StoreRes::PutIfMatch { result } => result.as_ref().err(),
StoreRes::PutIfNoneMatch { result } => result.as_ref().err(),
StoreRes::AppIfMatch { result } => result.as_ref().err(),
StoreRes::Put { result } => result.as_ref().err(),
StoreRes::Del { result } => result.as_ref().err(),
StoreRes::List { result } => result.as_ref().err(),
StoreRes::ListPrefixes { result } => result.as_ref().err(),
}
}
