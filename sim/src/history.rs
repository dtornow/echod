//! What each client saw, with virtual timestamps; and the instants the
//! nodes' own steps were decided at.
//!
//! An entry spans from the first attempt to the answer. A request answered
//! with "no answer" is retried with the same instant until it is answered,
//! which every operation admits, so the span is the only window in which the
//! operation can have taken effect.

use std::sync::{Arc, Mutex};

use echod_abstract::ExternalAction;
use serde_json::Value;

#[derive(Clone)]
pub struct Entry {
    pub id: u64,
    pub client: String,
    pub req: Arc<ExternalAction>,
    /// The instant the client sent this attempt at on the injected clock.
    /// A retry carries its own.
    pub now: u64,
    pub invoke: u64,
    pub ret: u64,
    /// `(status, data)`; `None` when no answer came.
    pub outcome: Option<(u16, Value)>,
    pub attempts: u32,
}

#[derive(Default)]
pub struct History {
    entries: Mutex<Vec<Entry>>,
    next: std::sync::atomic::AtomicU64,
    open: Mutex<std::collections::BTreeMap<u64, Entry>>,
    /// The instants a node decided a step of its own at (a sweep, a fire):
    /// clock moves the checker must know of, since a document's stamp may
    /// come to rest on one and a later request be decided at it.
    marks: Mutex<Vec<u64>>,
}

impl History {
    pub fn new() -> Self {
        Self::default()
    }

    /// Open an entry; it is recorded when closed.
    pub fn begin(&self, client: &str, req: Arc<ExternalAction>, now: u64, invoke: u64) -> u64 {
        let id = self.next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.open.lock().unwrap().insert(
            id,
            Entry {
                id,
                client: client.to_string(),
                req,
                now,
                invoke,
                ret: 0,
                outcome: None,
                attempts: 0,
            },
        );
        id
    }

    pub fn attempt(&self, id: u64) {
        if let Some(e) = self.open.lock().unwrap().get_mut(&id) {
            e.attempts += 1;
        }
    }

    pub fn end(&self, id: u64, ret: u64, outcome: Option<(u16, Value)>) {
        if let Some(mut e) = self.open.lock().unwrap().remove(&id) {
            e.ret = ret;
            e.outcome = outcome;
            self.entries.lock().unwrap().push(e);
        }
    }

    /// A node decided a step of its own at `now`.
    pub fn mark(&self, now: u64) {
        self.marks.lock().unwrap().push(now);
    }

    /// Entries never closed: a client killed mid-request. They are closed at
    /// `ret` with no outcome, since they may have taken effect.
    pub fn close_open(&self, ret: u64) {
        let open: Vec<Entry> = self.open.lock().unwrap().values().cloned().collect();
        for e in open {
            self.end(e.id, ret, None);
        }
    }

    pub fn entries(&self) -> Vec<Entry> {
        let mut v = self.entries.lock().unwrap().clone();
        v.sort_by_key(|e| (e.invoke, e.id));
        v
    }

    pub fn marks(&self) -> Vec<u64> {
        let mut v = self.marks.lock().unwrap().clone();
        v.sort_unstable();
        v.dedup();
        v
    }
}
