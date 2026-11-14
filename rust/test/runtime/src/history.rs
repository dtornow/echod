//! Typed client history and the instants of autonomous node steps.

use echod_types::{Request, Response};

#[derive(Clone, Debug)]
pub struct Entry {
    pub id: u64,
    pub client: String,
    pub req: Request,
    /// The instant the client sent this attempt at, `head.debug_time`: the
    /// instant the node decides it at. A retry carries its own.
    pub now: u64,
    pub invoke: u64,
    pub ret: u64,
    /// The production core's typed answer; `None` when no answer came.
    pub outcome: Option<Response>,
    pub attempts: u32,
}

#[derive(Default)]
pub struct History {
    entries: Vec<Entry>,
    next: u64,
    open: std::collections::BTreeMap<u64, Entry>,
    /// The instants a node decided a step of its own at (a sweep, a fire):
    /// clock moves the checker must know of, since a document's stamp may
    /// come to rest on one and a later request be decided at it.
    marks: Vec<u64>,
}

impl History {
    pub fn new() -> Self {
        Self::default()
    }

    /// Open an entry; it is recorded when closed.
    pub fn begin(&mut self, client: &str, req: Request, now: u64, invoke: u64) -> u64 {
        let id = self.next;
        self.next = self.next.wrapping_add(1);
        self.open.insert(
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

    pub fn attempt(&mut self, id: u64) {
        if let Some(e) = self.open.get_mut(&id) {
            e.attempts += 1;
        }
    }

    pub fn end(&mut self, id: u64, ret: u64, outcome: Option<Response>) {
        if let Some(mut e) = self.open.remove(&id) {
            e.ret = ret;
            e.outcome = outcome;
            self.entries.push(e);
        }
    }

    /// A node decided a step of its own at `now`.
    pub fn mark(&mut self, now: u64) {
        self.marks.push(now);
    }

    /// Entries never closed: a client killed mid-request. They are closed at
    /// `ret` with no outcome, since they may have taken effect.
    pub fn close_open(&mut self, ret: u64) {
        let open: Vec<Entry> = self.open.values().cloned().collect();
        for e in open {
            self.end(e.id, ret, None);
        }
    }

    pub fn entries(&self) -> Vec<Entry> {
        let mut v = self.entries.clone();
        v.sort_by_key(|e| (e.invoke, e.id));
        v
    }

    pub fn marks(&self) -> Vec<u64> {
        let mut v = self.marks.clone();
        v.sort_unstable();
        v.dedup();
        v
    }
}
