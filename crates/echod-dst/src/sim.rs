//! The run: servers over one store, clients, crashes, then the checks.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use echod_server::env::{Clock, Observer};
use echod_server::keys::{KeySpace, TimerEntry};
use echod_server::store::{MemoryStore, Store};
use echod_server::{Config, Server};
use resonate_core::types::{RequestEnvelope, RequestHead, PROTOCOL_VERSION};
use resonate_core::ResonateServer;
use serde::Serialize;

use crate::bus::RecordingBus;
use crate::checker::{check_origin, Verdict};
use crate::clock::SimClock;
use crate::history::History;
use crate::peers::SimPeers;
use crate::rng::Rng;
use crate::store::{Counters, Faults, FaultyStore};
use crate::workload::{Generator, Op, Seen};

#[derive(Clone, Debug)]
pub struct Options {
    pub seed: u64,
    pub servers: u32,
    pub clients: u32,
    pub operations: u64,
    pub origins: u64,
    pub promises_per_origin: u64,
    pub faults: Faults,
    /// Chance, per crash tick, that a node is killed and replaced.
    pub crash_percent: u64,
    pub crash_every_ms: u64,
    /// Promise timeouts fall within this many ms of their creation.
    pub timeout_ms: u64,
    pub ttl_ms: u64,
    pub retry_timeout_ms: u64,
    pub timer_bucket_ms: u64,
    pub heartbeat_ms: u64,
    pub node_ttl_ms: u64,
    /// A client's pause between requests, at most.
    pub think_ms: u64,
    /// How long the run idles after the last request so deadlines fire.
    pub settle_ms: u64,
    /// The search budget per origin.
    pub budget: u64,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            seed: 1,
            servers: 2,
            clients: 3,
            operations: 200,
            origins: 3,
            promises_per_origin: 3,
            faults: Faults { unavailable_percent: 2, lost_ack_percent: 2, conflict_percent: 2, latency_ms: 20 },
            crash_percent: 10,
            crash_every_ms: 500,
            timeout_ms: 3_000,
            ttl_ms: 4_000,
            retry_timeout_ms: 700,
            timer_bucket_ms: 2_000,
            heartbeat_ms: 200,
            node_ttl_ms: 800,
            think_ms: 60,
            settle_ms: 8_000,
            budget: 2_000_000,
        }
    }
}

#[derive(Debug, Default, Serialize)]
pub struct Report {
    pub seed: u64,
    pub ok: bool,
    pub entries: usize,
    pub sweeps: usize,
    pub crashes: u32,
    pub overlapping_pairs: u64,
    pub kinds_succeeded: BTreeSet<String>,
    pub kinds_missing: BTreeSet<String>,
    pub store_operations: u64,
    pub store_unavailable: u64,
    pub store_lost_acks: u64,
    pub store_conflicts: u64,
    pub executes: u64,
    pub unblocks: u64,
    pub checked_origins: usize,
    pub search_steps: u64,
    pub failures: Vec<String>,
}

/// Sweeps enter the history through the observer port.
struct SweepObserver {
    history: Arc<History>,
    clock: Arc<SimClock>,
}

impl Observer for SweepObserver {
    fn sweep_begin(&self, node: &str, origin: &str, now: u64) -> u64 {
        self.history.begin(origin, node, Op::Sweep, now, self.clock.now())
    }
    fn sweep_end(&self, handle: u64, committed: bool) {
        // A committed sweep took effect; a failed one may or may not have.
        let outcome = committed.then(|| (200u16, serde_json::json!({})));
        self.history.end(handle, self.clock.now(), outcome);
    }
}

struct Fleet {
    live: BTreeMap<String, Arc<Server>>,
    next_id: u32,
    crashes: u32,
}

struct World {
    opts: Options,
    inner: Arc<MemoryStore>,
    store: Arc<FaultyStore>,
    clock: Arc<SimClock>,
    bus: Arc<RecordingBus>,
    peers: Arc<SimPeers>,
    history: Arc<History>,
    keys: KeySpace,
    fleet: Mutex<Fleet>,
    issued: AtomicU64,
    appendable: bool,
}

impl World {
    async fn start_server(&self) -> Arc<Server> {
        let id = {
            let mut f = self.fleet.lock().unwrap();
            f.next_id += 1;
            format!("s{}", f.next_id)
        };
        let mut cfg = Config::memory("sim");
        cfg.node_id = Some(id.clone());
        cfg.url = Some(format!("sim://{id}/"));
        cfg.compact = if self.appendable { 8 } else { 0 };
        cfg.retry_timeout = self.opts.retry_timeout_ms;
        cfg.timer_bucket_ms = self.opts.timer_bucket_ms;
        cfg.heartbeat_ms = self.opts.heartbeat_ms;
        cfg.node_ttl_ms = self.opts.node_ttl_ms;
        cfg.debug = true; // the clock is the request's
        let observer = Arc::new(SweepObserver { history: Arc::clone(&self.history), clock: Arc::clone(&self.clock) });
        let store: Arc<dyn Store> = Arc::clone(&self.store) as Arc<dyn Store>;
        let server = Server::with_env(cfg, store, Arc::clone(&self.bus) as Arc<dyn resonate_core::ResonateRouter>, Arc::clone(&self.clock) as Arc<dyn echod_server::env::Clock>, Arc::clone(&self.peers) as Arc<dyn echod_server::env::Peers>, observer);
        // Init retries until the store answers: a node that cannot announce
        // itself is not up.
        loop {
            match server.init(false).await {
                Ok(()) => break,
                Err(_) => tokio::time::sleep(Duration::from_millis(50)).await,
            }
        }
        self.peers.register(&format!("sim://{id}/"), &server);
        self.fleet.lock().unwrap().live.insert(id, Arc::clone(&server));
        server
    }

    async fn crash_one(&self, rng: &mut Rng) {
        let victim = {
            let f = self.fleet.lock().unwrap();
            let ids: Vec<String> = f.live.keys().cloned().collect();
            if ids.is_empty() {
                return;
            }
            rng.pick(&ids).clone()
        };
        let server = self.fleet.lock().unwrap().live.remove(&victim);
        if let Some(server) = server {
            self.peers.unregister(&format!("sim://{victim}/"));
            server.crash().await;
            self.fleet.lock().unwrap().crashes += 1;
            tracing::info!(node = %victim, at = self.clock.now(), "crashed");
        }
        self.start_server().await;
    }

    /// The node a request goes to: the owner by hash, as a load balancer
    /// would route it, most of the time; any node otherwise.
    fn route(&self, origin: &str, rng: &mut Rng) -> Option<Arc<Server>> {
        let f = self.fleet.lock().unwrap();
        let live: Vec<&Arc<Server>> = f.live.values().collect();
        if live.is_empty() {
            return None;
        }
        let i = if rng.percent(80) { (echod_server::keys::fnv1a(origin) % live.len() as u64) as usize } else { rng.below(live.len() as u64) as usize };
        Some(Arc::clone(live[i]))
    }

    async fn client(self: Arc<Self>, name: String, mut rng: Rng) {
        let gen = Generator { origins: self.opts.origins, promises_per_origin: self.opts.promises_per_origin, timeout_ms: self.opts.timeout_ms, ttl_ms: self.opts.ttl_ms };
        let mut seen = Seen::default();
        while self.issued.fetch_add(1, Ordering::Relaxed) < self.opts.operations {
            let now = self.clock.now();
            let op = gen.next(&mut rng, &seen, now);
            let origin = op.origin();
            // Every attempt is its own entry: one that got no answer may have
            // taken effect, and a retry of it is not the same operation
            // again — an acquire retried after a lost answer is refused.
            let mut attempts = 0;
            loop {
                attempts += 1;
                let Some(server) = self.route(&origin, &mut rng) else {
                    tokio::time::sleep(Duration::from_millis(50)).await;
                    continue;
                };
                let entry = self.history.begin(&origin, &name, op.clone(), now, self.clock.now());
                self.history.attempt(entry);
                let req = RequestEnvelope {
                    kind: op.kind().to_string(),
                    head: RequestHead { corr_id: format!("c{entry}"), version: PROTOCOL_VERSION.to_string(), auth: None, debug_time: Some(now as i64) },
                    data: op.data(),
                };
                let mut crashed = server.crashed();
                let answer = tokio::select! {
                    biased;
                    _ = crashed.changed() => Err(resonate_core::Unavailable::new("node crashed")),
                    r = server.process_from(&req, false) => r.map(|(resp, _)| resp),
                };
                match answer {
                    Ok(resp) => {
                        seen.note(&resp.data);
                        self.history.end(entry, self.clock.now(), Some((resp.head.status as u16, resp.data)));
                        break;
                    }
                    Err(_) => {
                        self.history.end(entry, self.clock.now(), None);
                        if attempts >= 200 {
                            break;
                        }
                        tokio::time::sleep(Duration::from_millis(rng.range(1, 50))).await;
                    }
                }
            }
            tokio::time::sleep(Duration::from_millis(rng.range(0, self.opts.think_ms))).await;
        }
    }
}

/// One run, on its own runtime, under the paused clock.
pub fn run(opts: Options) -> Report {
    let rt = tokio::runtime::Builder::new_current_thread().enable_time().start_paused(true).build().expect("a runtime");
    rt.block_on(simulate(opts))
}

async fn simulate(opts: Options) -> Report {
    let mut rng = Rng::new(opts.seed);
    let appendable = rng.percent(50);
    let inner = Arc::new(if appendable { MemoryStore::appendable() } else { MemoryStore::new() });
    let store = Arc::new(FaultyStore::new(Arc::clone(&inner), opts.faults, rng.fork()));
    let clock = Arc::new(SimClock::new(1_700_000_000_000));
    let keys = KeySpace::new("", opts.timer_bucket_ms);
    let bus = Arc::new(RecordingBus::new(Arc::clone(&inner), keys.clone(), Arc::clone(&clock) as Arc<dyn echod_server::env::Clock>));
    let world = Arc::new(World {
        opts: opts.clone(),
        inner,
        store,
        clock,
        bus,
        peers: Arc::new(SimPeers::new()),
        history: Arc::new(History::new()),
        keys,
        fleet: Mutex::new(Fleet { live: BTreeMap::new(), next_id: 0, crashes: 0 }),
        issued: AtomicU64::new(0),
        appendable,
    });
    for _ in 0..opts.servers {
        world.start_server().await;
    }
    // Let the nodes meet and the membership take effect before the load
    // arrives: a member counts a TTL after it first announced.
    tokio::time::sleep(Duration::from_millis(opts.node_ttl_ms + opts.heartbeat_ms * 3)).await;

    let mut clients = Vec::new();
    for c in 0..opts.clients {
        clients.push(tokio::spawn(Arc::clone(&world).client(format!("client{c}"), rng.fork())));
    }
    let crasher = {
        let world = Arc::clone(&world);
        let mut rng = rng.fork();
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_millis(world.opts.crash_every_ms)).await;
                if world.issued.load(Ordering::Relaxed) >= world.opts.operations {
                    return;
                }
                if rng.percent(world.opts.crash_percent) {
                    world.crash_one(&mut rng).await;
                }
            }
        })
    };
    for c in clients {
        let _ = c.await;
    }
    let _ = crasher.await;
    tokio::time::sleep(Duration::from_millis(opts.settle_ms)).await;
    let live: Vec<Arc<Server>> = world.fleet.lock().unwrap().live.values().cloned().collect();
    for s in &live {
        let _ = s.stop().await;
    }
    world.history.close_open(world.clock.now());

    check(&world).await
}

async fn check(world: &World) -> Report {
    let opts = &world.opts;
    let cfg = echod_kernel::Config { retry_timeout: opts.retry_timeout_ms, compact: 0 };
    let entries = world.history.entries();
    let mut report = Report { seed: opts.seed, entries: entries.len(), ..Default::default() };
    report.sweeps = entries.iter().filter(|e| matches!(e.op, Op::Sweep)).count();
    report.crashes = world.fleet.lock().unwrap().crashes;
    let c: Counters = world.store.counters();
    report.store_operations = c.operations;
    report.store_unavailable = c.unavailable;
    report.store_lost_acks = c.lost_acks;
    report.store_conflicts = c.conflicts;
    {
        let t = world.bus.tally.lock().unwrap();
        report.executes = t.executes;
        report.unblocks = t.unblocks;
        for v in &t.violations {
            report.failures.push(format!("message: {v}"));
        }
    }

    // Coverage: every kind answered 200 at least once, and the history overlapped.
    let all_kinds: BTreeSet<String> = [
        "promise.get", "promise.create", "promise.settle", "promise.register_callback", "promise.register_listener",
        "task.get", "task.create", "task.acquire", "task.fulfill", "task.release", "task.heartbeat", "task.suspend", "task.fence", "task.halt", "task.continue",
    ].iter().map(|s| s.to_string()).collect();
    for e in &entries {
        if let Some((200, _)) = &e.outcome {
            report.kinds_succeeded.insert(e.op.kind().to_string());
        }
    }
    report.kinds_missing = all_kinds.difference(&report.kinds_succeeded).cloned().collect();
    let clients: Vec<&crate::history::Entry> = entries.iter().filter(|e| !matches!(e.op, Op::Sweep)).collect();
    for (i, a) in clients.iter().enumerate() {
        for b in &clients[i + 1..] {
            if b.invoke < a.ret && a.invoke <= b.invoke {
                report.overlapping_pairs += 1;
            }
        }
    }
    if report.overlapping_pairs == 0 && opts.clients > 1 {
        report.failures.push("the history never overlapped: nothing concurrent was checked".into());
    }

    // Linearizability, per origin, against the bucket's final rows.
    let mut by_origin: BTreeMap<String, Vec<crate::history::Entry>> = BTreeMap::new();
    for e in &entries {
        by_origin.entry(e.origin.clone()).or_default().push(e.clone());
    }
    for (origin, es) in &by_origin {
        let rows = match world.inner.get(&world.keys.doc_key(origin)).await {
            Ok(Some((bytes, _))) => echod_server::doc::decode(&bytes).map(|l| l.rows).unwrap_or_default(),
            _ => Vec::new(),
        };
        report.checked_origins += 1;
        match check_origin(origin, es, &rows, &cfg, opts.budget) {
            Verdict::Linearizable { steps } => report.search_steps += steps,
            Verdict::NotLinearizable { origin, steps, detail } => {
                report.search_steps += steps;
                report.failures.push(format!("origin {origin}: not linearizable after {steps} steps: {detail}"));
            }
            Verdict::Undecided { origin, steps } => {
                report.search_steps += steps;
                report.failures.push(format!("origin {origin}: undecided after {steps} steps"));
            }
        }
    }

    // Every deadline a document owes has a key.
    let timer_keys = world.inner.list("t/", usize::MAX).await.unwrap_or_default();
    let armed: BTreeSet<(String, u64)> = timer_keys
        .iter()
        .filter_map(|k| match world.keys.parse_timer_key(k) {
            Some(TimerEntry::Origin { origin, deadline, .. }) => Some((origin, deadline)),
            _ => None,
        })
        .collect();
    for key in world.inner.list("wf/", usize::MAX).await.unwrap_or_default() {
        let Ok(Some((bytes, _))) = world.inner.get(&key).await else { continue };
        let rows = echod_server::doc::decode(&bytes).map(|l| l.rows).unwrap_or_default();
        let origin = key.trim_start_matches("wf/");
        let origin = echod_server::keys::decode_key(origin).unwrap_or_else(|| origin.to_string());
        if let Some(d) = echod_server::step::next_deadline(&rows) {
            if !armed.contains(&(origin.clone(), d)) {
                report.failures.push(format!("origin {origin}: owes a deadline at {d} and the bucket holds no key for it"));
            }
        }
    }

    report.ok = report.failures.is_empty();
    report
}
