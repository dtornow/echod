//! What each client saw, and what the nodes did, with virtual timestamps.
//!
//! A client's entry spans from the first attempt to the answer. A request
//! answered with "no answer" is retried with the same instant until it is
//! answered, which every operation admits, so the span is the only window in
//! which the operation can have taken effect. A node's step (a request's,
//! a sweep, a fire, an advance) is recorded as the node reports it through
//! the notes port: the instant it was decided at, the document's version it
//! made or saw, and whether its write landed.

use std::sync::Mutex;

use resonate::{Request, Step};
use serde_json::Value;

#[derive(Clone, Debug)]
pub struct Entry {
    pub id: u64,
    pub client: String,
    pub req: Request,
    /// The instant the client sent it at: `head.debug_time`.
    pub now: u64,
    pub invoke: u64,
    pub ret: u64,
    /// `(status, data)`; `None` when no answer came.
    pub outcome: Option<(u16, Value)>,
    pub attempts: u32,
}

/// A step a node took, as it reported it.
#[derive(Clone, Debug)]
pub struct StepRec {
    /// The order the node reported it in.
    pub order: u64,
    /// The instant it was decided at.
    pub now: u64,
    /// The document it ran on, and the version it made (`wrote`) or saw (a
    /// step that wrote nothing): two steps on one document at one instant
    /// are ordered by it.
    pub target: String,
    pub seq: u64,
    pub wrote: bool,
    /// The model's step, if the document holds objects: none on a
    /// schedule's document for a request there, whose step is the request.
    pub step: Option<Step>,
    /// The request whose step this is, if a request's.
    pub request: Option<u64>,
    /// The nonce its write carries, by which the store tells whether a write
    /// the node saw fail, or never saw answered, landed all the same.
    pub nonce: u64,
    /// Whether the node saw its write land.
    pub committed: bool,
}

#[derive(Default)]
pub struct History {
    entries: Mutex<Vec<Entry>>,
    next: std::sync::atomic::AtomicU64,
    open: Mutex<std::collections::BTreeMap<u64, Entry>>,
    steps: Mutex<Vec<StepRec>>,
}

impl History {
    pub fn new() -> Self {
        Self::default()
    }

    /// Open an entry; it is recorded when closed.
    pub fn begin(&self, client: &str, req: Request, now: u64, invoke: u64) -> u64 {
        let id = self.next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.open.lock().unwrap().insert(id, Entry { id, client: client.to_string(), req, now, invoke, ret: 0, outcome: None, attempts: 0 });
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

    /// The entry a correlation id names, if it is one of ours.
    pub fn entry_of(corr: &str) -> Option<u64> {
        corr.strip_prefix('c').and_then(|n| n.parse().ok())
    }

    /// A node took a step; `order` is assigned here, in report order.
    #[allow(clippy::too_many_arguments)]
    pub fn step(&self, now: u64, target: &str, seq: u64, wrote: bool, step: Option<Step>, request: Option<u64>, nonce: u64, committed: bool) {
        let mut steps = self.steps.lock().unwrap();
        let order = steps.len() as u64;
        steps.push(StepRec { order, now, target: target.to_string(), seq, wrote, step, request, nonce, committed });
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

    pub fn steps(&self) -> Vec<StepRec> {
        self.steps.lock().unwrap().clone()
    }
}
