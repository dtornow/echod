//! A bus that takes every message, records it as the model's dispatch, and
//! checks it against the bucket.
//!
//! Not a bus that serves nothing: that would leave the one path that turns a
//! committed transition into something a worker can read untested. Every
//! message is a `Receive` in the checker's trace; and, read from the bucket at
//! the moment of sending, every `execute` must name a task that is really
//! there, every `unblock` a promise that is really settled.

use std::sync::{Arc, Mutex};

use async_trait::async_trait;
use echod_kernel::PromiseState;
use echod::env::Clock;
use echod::store::{MemoryStore, Store};
use echod_logic::keys::{origin_of, KeySpace};
use resonate::Dispatch;
use resonate_core::types::Message;
use resonate_core::{ResonateRouter, Unavailable};

use crate::wire::prec;

#[derive(Debug, Clone)]
pub struct Sent {
    pub at: u64,
    pub address: String,
    pub kind: String,
    pub id: String,
    /// The message as the model types it.
    pub msg: Dispatch,
}

#[derive(Default)]
pub struct Tally {
    pub executes: u64,
    pub unblocks: u64,
    pub violations: Vec<String>,
}

pub struct RecordingBus {
    store: Arc<MemoryStore>,
    keys: KeySpace,
    clock: Arc<dyn Clock>,
    pub sent: Mutex<Vec<Sent>>,
    pub tally: Mutex<Tally>,
}

impl RecordingBus {
    pub fn new(store: Arc<MemoryStore>, keys: KeySpace, clock: Arc<dyn Clock>) -> Self {
        Self { store, keys, clock, sent: Mutex::new(Vec::new()), tally: Mutex::new(Tally::default()) }
    }

    async fn rows(&self, origin: &str) -> Vec<echod_kernel::Promise> {
        match self.store.get(&self.keys.doc_key(origin)).await {
            Ok(Some((bytes, _))) => echod_logic::doc::decode(&bytes).map(|l| l.rows).unwrap_or_default(),
            _ => Vec::new(),
        }
    }
}

#[async_trait]
impl ResonateRouter for RecordingBus {
    async fn route(&self, address: &str, msg: &Message) -> Result<(), Unavailable> {
        let now = self.clock.now();
        let (kind, id, dispatch) = match msg {
            Message::Execute(m) => ("execute", m.data.task.id.clone(), Dispatch::Execute { id: m.data.task.id.clone(), version: m.data.task.version as u32 }),
            Message::Unblock(m) => {
                let promise = serde_json::to_value(&m.data.promise).ok().and_then(|v| prec(&v)).unwrap_or_else(|| panic!("an unblock with a promise record: {msg:?}"));
                ("unblock", m.data.promise.id.clone(), Dispatch::Unblock { address: address.to_string(), promise })
            }
        };
        let rows = self.rows(origin_of(&id)).await;
        let found = rows.iter().find(|p| p.id == id);
        let mut tally = self.tally.lock().unwrap();
        match msg {
            Message::Execute(_) => {
                tally.executes += 1;
                match found {
                    Some(p) if p.task.is_some() => {}
                    _ => tally.violations.push(format!("execute for {id} at {now}: no such task in the bucket")),
                }
            }
            Message::Unblock(m) => {
                tally.unblocks += 1;
                let settled = found.map(|p| p.state != PromiseState::Pending || p.timeout_at <= now).unwrap_or(false);
                if !settled {
                    tally.violations.push(format!("unblock for {id} at {now}: the promise is not settled in the bucket"));
                }
                if m.data.promise.state == resonate_core::types::PromiseState::Pending {
                    tally.violations.push(format!("unblock for {id} at {now}: carries a pending promise"));
                }
            }
        }
        drop(tally);
        self.sent.lock().unwrap().push(Sent { at: now, address: address.to_string(), kind: kind.to_string(), id, msg: dispatch });
        Ok(())
    }
}
