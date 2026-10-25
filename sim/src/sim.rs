//! The run: nodes over one store, clients, crashes, then the checks.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use echod::env::{Clock, Notes};
use echod::store::{MemoryStore, Store};
use echod::{Config, Node as Server};
use echod_logic::keys::{KeySpace, TimerEntry};
use echod_logic::{FlightId, Note};
use resonate_core::types::{RequestEnvelope, RequestHead, PROTOCOL_VERSION};
use resonate_core::ResonateServer;
use serde::Serialize;

use resonate::{Request, Step};

use crate::bus::RecordingBus;
use crate::checker::{self, Verdict};
use crate::clock::{NodeClock, SimClock};
use crate::history::History;
use crate::rng::Rng;
use crate::store::{Counters, Faults, FaultyStore, NodeStore};
use crate::wire::encode;
use crate::workload::{target_of, Generator, Seen, SCHEDULES, WORKER};

#[derive(Clone, Debug)]
pub struct Options {
    pub seed: u64,
    pub servers: u32,
    pub clients: u32,
    pub operations: u64,
    pub origins: u64,
    pub promises_per_origin: u64,
    pub faults: Faults,
    /// Every `chaos_every_ms`, each of these is rolled once, in percent:
    /// a node is killed and replaced; a node stops cleanly; a node joins; a
    /// node loses the store for a while; a node's clock jumps, forwards or
    /// back.
    pub crash_percent: u64,
    pub stop_percent: u64,
    pub join_percent: u64,
    pub outage_percent: u64,
    pub jump_percent: u64,
    pub chaos_every_ms: u64,
    /// How long an outage lasts, at most.
    pub disruption_ms: u64,
    /// A node's clock is off the reference by up to this, either way.
    pub skew_ms: u64,
    /// A node's clock gains or loses up to this many parts per million.
    pub drift_ppm: u64,
    /// A jump moves a node's clock by up to this, either way.
    pub jump_ms: u64,
    /// The fleet never grows past this.
    pub max_servers: u32,
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
    /// The checker's budget: nodes to explore, at most.
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
            stop_percent: 5,
            join_percent: 8,
            outage_percent: 10,
            jump_percent: 15,
            chaos_every_ms: 500,
            disruption_ms: 2_500,
            // Clock chaos off: the checker's model keeps one clock (`checker.rs`).
            skew_ms: 0,
            drift_ppm: 0,
            jump_ms: 0,
            max_servers: 4,
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
    pub fires: usize,
    pub crashes: u32,
    pub stops: u32,
    pub joins: u32,
    pub outages: u32,
    pub jumps: u32,
    pub overlapping_pairs: u64,
    pub kinds_succeeded: BTreeSet<String>,
    pub kinds_missing: BTreeSet<String>,
    pub store_operations: u64,
    pub store_unavailable: u64,
    pub store_lost_acks: u64,
    pub store_conflicts: u64,
    pub executes: u64,
    pub unblocks: u64,
    /// The nodes' steps that landed, in the checker's trace.
    pub steps: usize,
    /// Events in the checker's trace.
    pub events: usize,
    /// Nodes the checker explored.
    pub search_steps: u64,
    pub failures: Vec<String>,
}

/// The nodes' steps enter the history through the notes port: each begins
/// when decided and ends when its commit is known, paired by flight. A
/// request's step is the request's own sweep after it; a fire is the
/// occurrence and then its origin's sweep, then the advance on the
/// schedule's document. Sweeps and fires are counted.
struct StepNotes {
    history: Arc<History>,
    sweeps: AtomicU64,
    fires: AtomicU64,
    /// Steps decided and not yet ended, by node and flight (flight ids are a
    /// node's own).
    begun: Mutex<HashMap<(String, FlightId), Begun>>,
}

struct Begun {
    now: u64,
    target: String,
    seq: u64,
    wrote: bool,
    nonce: u64,
    ids: Option<Vec<String>>,
    what: What,
}

enum What {
    Request(u64),
    Sweep,
    Fire { schedule: String, at: u64, promise: String },
    Advance { schedule: String, at: u64 },
}

impl StepNotes {
    fn begin(&self, node: &str, flight: FlightId, b: Begun) {
        self.begun.lock().unwrap().insert((node.to_string(), flight), b);
    }

    fn end(&self, node: &str, flight: FlightId, committed: bool) {
        let Some(b) = self.begun.lock().unwrap().remove(&(node.to_string(), flight)) else { return };
        self.record(b, committed);
    }

    /// The steps begun and never ended (the node died first): the store
    /// says whether they landed.
    fn flush(&self) {
        let begun: Vec<Begun> = std::mem::take(&mut *self.begun.lock().unwrap()).into_values().collect();
        for b in begun {
            self.record(b, false);
        }
    }

    fn record(&self, b: Begun, committed: bool) {
        // a step on a document with no objects yet has nothing to run on
        let ids = b.ids.filter(|ids| !ids.is_empty());
        let step = |step: Option<Step>, request: Option<u64>| self.history.step(b.now, &b.target, b.seq, b.wrote, step, request, b.nonce, committed);
        match b.what {
            // a request, then the drain of its document: what the request
            // left to do, not what the clock made due
            What::Request(entry) => step(ids.map(Step::Drain), Some(entry)),
            // a sweep does everything due; one on a schedule's document runs
            // nothing of the model's, but its write stamps a version the
            // reads of it sit at
            What::Sweep => step(ids.map(Step::Objects), None),
            What::Fire { schedule, at, promise } => {
                step(Some(Step::Fire { schedule, at, promise }), None);
                step(ids.map(Step::Drain), None);
            }
            What::Advance { schedule, at } => step(Some(Step::Advance { schedule, at }), None),
        }
    }
}

impl Notes for StepNotes {
    fn note(&self, node: &str, n: &Note) {
        match n {
            Note::RequestBegin { flight, corr, target, now, seq, wrote, nonce, ids } => {
                if let Some(entry) = History::entry_of(corr) {
                    self.begin(node, *flight, Begun { now: *now, target: target.clone(), seq: *seq, wrote: *wrote, nonce: *nonce, ids: ids.clone(), what: What::Request(entry) });
                }
            }
            Note::SweepBegin { flight, target, now, seq, wrote, nonce, ids } => {
                self.sweeps.fetch_add(1, Ordering::Relaxed);
                self.begin(node, *flight, Begun { now: *now, target: target.clone(), seq: *seq, wrote: *wrote, nonce: *nonce, ids: ids.clone(), what: What::Sweep });
            }
            Note::FireBegin { flight, origin, now, seq, nonce, ids, row, at, promise_id, .. } => {
                self.fires.fetch_add(1, Ordering::Relaxed);
                let what = What::Fire { schedule: row.id.clone(), at: *at, promise: promise_id.clone() };
                self.begin(node, *flight, Begun { now: *now, target: origin.clone(), seq: *seq, wrote: true, nonce: *nonce, ids: Some(ids.clone()), what });
            }
            Note::AdvanceBegin { flight, schedule, target, now, seq, nonce, at, .. } => {
                let what = What::Advance { schedule: schedule.clone(), at: *at };
                self.begin(node, *flight, Begun { now: *now, target: target.clone(), seq: *seq, wrote: true, nonce: *nonce, ids: None, what });
            }
            Note::RequestEnd { flight, committed } | Note::SweepEnd { flight, committed } | Note::FireEnd { flight, committed } | Note::AdvanceEnd { flight, committed } => self.end(node, *flight, *committed),
            _ => {}
        }
    }
}

/// One node, and the clock and store view it alone sees.
struct Node {
    server: Arc<Server>,
    clock: Arc<NodeClock>,
    store: Arc<NodeStore>,
}

#[derive(Default)]
struct Fleet {
    live: BTreeMap<String, Node>,
    next_id: u32,
    crashes: u32,
    stops: u32,
    joins: u32,
    outages: u32,
    jumps: u32,
}

struct World {
    opts: Options,
    inner: Arc<MemoryStore>,
    store: Arc<FaultyStore>,
    clock: Arc<SimClock>,
    bus: Arc<RecordingBus>,
    history: Arc<History>,
    notes: Arc<StepNotes>,
    keys: KeySpace,
    fleet: Mutex<Fleet>,
    issued: AtomicU64,
    appendable: bool,
    rng: Mutex<Rng>,
}

impl World {
    async fn start_server(&self) -> Arc<Server> {
        let id = {
            let mut f = self.fleet.lock().unwrap();
            f.next_id += 1;
            format!("s{}", f.next_id)
        };
        let (skew, drift) = {
            let mut rng = self.rng.lock().unwrap();
            let skew = rng.range(0, 2 * self.opts.skew_ms) as i64 - self.opts.skew_ms as i64;
            let drift = rng.range(0, 2 * self.opts.drift_ppm) as i64 - self.opts.drift_ppm as i64;
            (skew, drift)
        };
        let clock = Arc::new(NodeClock::new(Arc::clone(&self.clock), skew, drift, self.opts.jump_ms as i64));
        let node_store = Arc::new(NodeStore::new(Arc::clone(&self.store)));
        let mut cfg = Config::memory("sim");
        cfg.node_id = Some(id.clone());
        cfg.url = Some(format!("sim://{id}/"));
        cfg.compact = if self.appendable { 8 } else { 0 };
        cfg.retry_timeout = self.opts.retry_timeout_ms;
        cfg.timer_bucket_ms = self.opts.timer_bucket_ms;
        cfg.heartbeat_ms = self.opts.heartbeat_ms;
        cfg.node_ttl_ms = self.opts.node_ttl_ms;
        cfg.debug = true; // the clock is the request's
        let store: Arc<dyn Store> = Arc::clone(&node_store) as Arc<dyn Store>;
        let server = Server::with_env(cfg, store, Arc::clone(&self.bus) as Arc<dyn resonate_core::ResonateRouter>, Arc::clone(&clock) as Arc<dyn Clock>, Arc::clone(&self.notes) as Arc<dyn Notes>);
        // A node that cannot reach the store keeps trying on its own.
        server.init(false).await.expect("a node starts");
        tracing::info!(node = %id, skew, drift, at = self.clock.now(), "started");
        self.fleet.lock().unwrap().live.insert(id, Node { server: Arc::clone(&server), clock, store: node_store });
        server
    }

    fn live_ids(&self) -> Vec<String> {
        self.fleet.lock().unwrap().live.keys().cloned().collect()
    }

    fn pick_node(&self, rng: &mut Rng) -> Option<String> {
        let ids = self.live_ids();
        (!ids.is_empty()).then(|| rng.pick(&ids).clone())
    }

    /// Kill a node where it stands and start a replacement.
    async fn crash_one(&self, rng: &mut Rng) {
        let Some(victim) = self.pick_node(rng) else { return };
        let node = self.fleet.lock().unwrap().live.remove(&victim);
        if let Some(node) = node {
            node.server.crash().await;
            self.fleet.lock().unwrap().crashes += 1;
            tracing::info!(node = %victim, at = self.clock.now(), "crashed");
        }
        self.start_server().await;
    }

    /// Stop a node cleanly: it withdraws its announcement. Never the last one.
    async fn stop_one(&self, rng: &mut Rng) {
        if self.live_ids().len() <= 1 {
            return;
        }
        let Some(victim) = self.pick_node(rng) else { return };
        let node = self.fleet.lock().unwrap().live.remove(&victim);
        if let Some(node) = node {
            let _ = node.server.stop().await;
            self.fleet.lock().unwrap().stops += 1;
            tracing::info!(node = %victim, at = self.clock.now(), "stopped");
        }
    }

    /// A node joins, if the fleet has room.
    async fn join_one(&self) {
        if self.live_ids().len() as u32 >= self.opts.max_servers {
            return;
        }
        self.start_server().await;
        self.fleet.lock().unwrap().joins += 1;
    }

    /// A node loses the store for a while: long enough, sometimes, for its
    /// view of the membership to go stale.
    fn outage(self: &Arc<Self>, rng: &mut Rng) {
        let Some(id) = self.pick_node(rng) else { return };
        let store = match self.fleet.lock().unwrap().live.get(&id) {
            Some(n) => Arc::clone(&n.store),
            None => return,
        };
        let for_ms = rng.range(100, self.opts.disruption_ms);
        store.set_cut(true);
        self.fleet.lock().unwrap().outages += 1;
        tracing::info!(node = %id, for_ms, at = self.clock.now(), "cut off from the store");
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(for_ms)).await;
            store.set_cut(false);
        });
    }

    /// A node's clock jumps, forwards or back.
    fn jump(&self, rng: &mut Rng) {
        let Some(id) = self.pick_node(rng) else { return };
        let delta = rng.range(0, 2 * self.opts.jump_ms) as i64 - self.opts.jump_ms as i64;
        if let Some(n) = self.fleet.lock().unwrap().live.get(&id) {
            n.clock.jump(delta);
        }
        self.fleet.lock().unwrap().jumps += 1;
        tracing::info!(node = %id, delta, at = self.clock.now(), "clock jumped");
    }

    /// Heal every outage, so the run can settle.
    fn heal(&self) {
        let f = self.fleet.lock().unwrap();
        for n in f.live.values() {
            n.store.set_cut(false);
        }
    }

    /// The node a request goes to: the owner by hash, as a load balancer
    /// would route it, most of the time; any node otherwise.
    fn route(&self, origin: &str, rng: &mut Rng) -> Option<Arc<Server>> {
        let f = self.fleet.lock().unwrap();
        let live: Vec<&Node> = f.live.values().collect();
        if live.is_empty() {
            return None;
        }
        let i = if rng.percent(80) { (echod_logic::keys::fnv1a(origin) % live.len() as u64) as usize } else { rng.below(live.len() as u64) as usize };
        Some(Arc::clone(&live[i].server))
    }

    async fn client(self: Arc<Self>, name: String, mut rng: Rng) {
        let gen = Generator { origins: self.opts.origins, promises_per_origin: self.opts.promises_per_origin, timeout_ms: self.opts.timeout_ms, ttl_ms: self.opts.ttl_ms };
        let mut seen = Seen::default();
        while self.issued.fetch_add(1, Ordering::Relaxed) < self.opts.operations {
            let now = self.clock.now();
            let req = gen.next(&mut rng, &seen, now);
            if let Some(data) = self.issue(&name, req, now, &mut rng).await {
                seen.note(&data);
            }
            tokio::time::sleep(Duration::from_millis(rng.range(0, self.opts.think_ms))).await;
        }
    }

    /// One request, decided at `now`, retried until answered. Every attempt
    /// is its own entry: one that got no answer may have taken effect, and a
    /// retry of it is not the same operation again (an acquire retried after
    /// a lost answer is refused). The answer's data, if one came.
    async fn issue(&self, name: &str, req: Request, now: u64, rng: &mut Rng) -> Option<serde_json::Value> {
        let target = target_of(&req);
        let (kind, data) = encode(&req, WORKER);
        let mut attempts = 0;
        loop {
            attempts += 1;
            let Some(server) = self.route(&target, rng) else {
                tokio::time::sleep(Duration::from_millis(50)).await;
                if attempts >= 200 {
                    return None;
                }
                continue;
            };
            let entry = self.history.begin(name, req.clone(), now, self.clock.now());
            self.history.attempt(entry);
            let envelope = RequestEnvelope {
                kind: kind.to_string(),
                head: RequestHead { corr_id: format!("c{entry}"), version: PROTOCOL_VERSION.to_string(), auth: None, debug_time: Some(now as i64) },
                data: data.clone(),
            };
            let mut crashed = server.crashed();
            let answer = tokio::select! {
                biased;
                _ = crashed.changed() => Err(resonate_core::Unavailable::new("node crashed")),
                r = server.process(&envelope) => r,
            };
            match answer {
                Ok(resp) => {
                    self.history.end(entry, self.clock.now(), Some((resp.head.status as u16, resp.data.clone())));
                    return Some(resp.data);
                }
                Err(_) => {
                    self.history.end(entry, self.clock.now(), None);
                    if attempts >= 200 {
                        return None;
                    }
                    tokio::time::sleep(Duration::from_millis(rng.range(1, 50))).await;
                }
            }
        }
    }

    /// The finishing reads: every id the run may have named, read once the
    /// run has settled, so what the bucket holds is what the model shows.
    async fn final_reads(&self, rng: &mut Rng) {
        let gen = Generator { origins: self.opts.origins, promises_per_origin: self.opts.promises_per_origin, timeout_ms: self.opts.timeout_ms, ttl_ms: self.opts.ttl_ms };
        let mut reads = Vec::new();
        for id in gen.ids() {
            reads.push(Request::GetPromise(id.clone()));
            reads.push(Request::GetTask(id));
        }
        for id in SCHEDULES {
            reads.push(Request::GetSchedule(id.to_string()));
        }
        for req in reads {
            let now = self.clock.now();
            self.issue("final", req, now, rng).await;
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
    let history = Arc::new(History::new());
    let keys = KeySpace::new("", opts.timer_bucket_ms);
    let bus = Arc::new(RecordingBus::new(Arc::clone(&inner), keys.clone(), Arc::clone(&clock) as Arc<dyn Clock>));
    let world = Arc::new(World {
        opts: opts.clone(),
        inner,
        store,
        clock,
        bus,
        history: Arc::clone(&history),
        notes: Arc::new(StepNotes { history, sweeps: AtomicU64::new(0), fires: AtomicU64::new(0), begun: Mutex::new(HashMap::new()) }),
        keys,
        fleet: Mutex::new(Fleet::default()),
        issued: AtomicU64::new(0),
        appendable,
        rng: Mutex::new(rng.fork()),
    });
    for _ in 0..opts.servers {
        world.start_server().await;
    }
    // Let the nodes meet before the load arrives: a configuration naming
    // them. Nothing is unsafe before that; requests would just not route.
    tokio::time::sleep(Duration::from_millis(opts.node_ttl_ms + opts.heartbeat_ms * 4)).await;

    let mut clients = Vec::new();
    for c in 0..opts.clients {
        clients.push(tokio::spawn(Arc::clone(&world).client(format!("client{c}"), rng.fork())));
    }
    let chaos = {
        let world = Arc::clone(&world);
        let mut rng = rng.fork();
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_millis(world.opts.chaos_every_ms)).await;
                if world.issued.load(Ordering::Relaxed) >= world.opts.operations {
                    return;
                }
                let o = &world.opts;
                if rng.percent(o.crash_percent) {
                    world.crash_one(&mut rng).await;
                }
                if rng.percent(o.stop_percent) {
                    world.stop_one(&mut rng).await;
                }
                if rng.percent(o.join_percent) {
                    world.join_one().await;
                }
                if rng.percent(o.outage_percent) {
                    world.outage(&mut rng);
                }
                if rng.percent(o.jump_percent) {
                    world.jump(&mut rng);
                }
            }
        })
    };
    for c in clients {
        let _ = c.await;
    }
    let _ = chaos.await;
    world.heal();
    if world.live_ids().is_empty() {
        world.start_server().await;
    }
    tokio::time::sleep(Duration::from_millis(opts.settle_ms)).await;
    world.final_reads(&mut rng).await;
    let live: Vec<Arc<Server>> = world.fleet.lock().unwrap().live.values().map(|n| Arc::clone(&n.server)).collect();
    for s in &live {
        let _ = s.stop().await;
    }
    world.history.close_open(world.clock.now());

    check(&world).await
}

async fn check(world: &World) -> Report {
    let opts = &world.opts;
    let entries = world.history.entries();
    let mut report = Report { seed: opts.seed, entries: entries.len(), ..Default::default() };
    report.sweeps = world.notes.sweeps.load(Ordering::Relaxed) as usize;
    report.fires = world.notes.fires.load(Ordering::Relaxed) as usize;
    {
        let f = world.fleet.lock().unwrap();
        report.crashes = f.crashes;
        report.stops = f.stops;
        report.joins = f.joins;
        report.outages = f.outages;
        report.jumps = f.jumps;
    }
    let c: Counters = world.store.counters();
    report.store_operations = c.operations;
    report.store_unavailable = c.unavailable;
    report.store_lost_acks = c.lost_acks;
    report.store_conflicts = c.conflicts;
    let sent = {
        let t = world.bus.tally.lock().unwrap();
        report.executes = t.executes;
        report.unblocks = t.unblocks;
        for v in &t.violations {
            report.failures.push(format!("message: {v}"));
        }
        world.bus.sent.lock().unwrap().clone()
    };

    // Coverage: every kind answered 200 at least once, and the history overlapped.
    let all_kinds: BTreeSet<String> = [
        "promise.get", "promise.create", "promise.settle", "promise.register_callback", "promise.register_listener",
        "task.get", "task.create", "task.acquire", "task.fulfill", "task.release", "task.heartbeat", "task.suspend", "task.fence", "task.halt", "task.continue",
        "schedule.get", "schedule.create", "schedule.delete",
    ].iter().map(|s| s.to_string()).collect();
    for e in &entries {
        if let Some((200, _)) = &e.outcome {
            report.kinds_succeeded.insert(encode(&e.req, WORKER).0.to_string());
        }
    }
    report.kinds_missing = all_kinds.difference(&report.kinds_succeeded).cloned().collect();
    let clients: Vec<&crate::history::Entry> = entries.iter().filter(|e| e.client != "final").collect();
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

    // The run as a trace of the model, checked by accordant.
    // The steps that landed: the ones the node saw commit, and the ones
    // whose write the store took although the node never learnt of it.
    world.notes.flush();
    let all = world.history.steps();
    if std::env::var_os("ECHOD_SIM_DUMP").is_some() {
        for s in &all {
            eprintln!("step {s:?} landed={}", world.store.has_landed(s.nonce));
        }
    }
    let steps: Vec<_> = all.into_iter().filter(|s| s.committed || world.store.has_landed(s.nonce)).collect();
    report.steps = steps.len();
    let trace = checker::trace(&entries, &steps, &sent);
    report.events = trace.len();
    match checker::check(&trace, opts.retry_timeout_ms, opts.budget) {
        Verdict::Ok { explored } => report.search_steps = explored as u64,
        Verdict::Ko(v) => {
            report.failures.push(format!("no execution of the model explains event {} of {}: {}: {}", v.index, trace.len(), v.event, v.reason));
            // `ECHOD_SIM_DUMP=1`: the trace up to the event, one per line, and
            // the candidates that could not explain it
            if std::env::var_os("ECHOD_SIM_DUMP").is_some() {
                eprint!("{}", checker::show(&trace, v.index));
                for n in v.profile.iter().take(6) {
                    eprintln!("candidate: {n}");
                }
            }
        }
        Verdict::Unknown(v) => {
            report.failures.push(format!("undecided at event {} of {}: {}", v.index, trace.len(), v.reason));
            if std::env::var_os("ECHOD_SIM_DUMP").is_some() {
                eprint!("{}", checker::show(&trace, v.index));
                for n in v.profile.iter().take(6) {
                    eprintln!("candidate: {n}");
                }
            }
        }
    }

    // Every deadline a document owes has a key.
    let timer_keys = world.inner.list("t/", usize::MAX).await.unwrap_or_default();
    let armed: BTreeSet<(String, u64)> = timer_keys
        .iter()
        .filter_map(|k| match world.keys.parse_timer_key(k) {
            Some(TimerEntry::Origin { origin, deadline, .. }) => Some((origin, deadline)),
            Some(TimerEntry::Schedule { id, deadline, .. }) => Some((format!("sched:{id}"), deadline)),
            None => None,
        })
        .collect();
    for key in world.inner.list("wf/", usize::MAX).await.unwrap_or_default() {
        let Ok(Some((bytes, _))) = world.inner.get(&key).await else { continue };
        let rows = echod_logic::doc::decode::<echod_kernel::Promise>(&bytes).map(|l| l.rows).unwrap_or_default();
        let origin = key.trim_start_matches("wf/");
        let origin = echod_logic::keys::decode_key(origin).unwrap_or_else(|| origin.to_string());
        if let Some(d) = echod_kernel::steps::next_deadline(&echod_kernel::State { objects: rows, schedules: Vec::new(), outbox: Vec::new() }) {
            if !armed.contains(&(origin.clone(), d)) {
                report.failures.push(format!("origin {origin}: owes a deadline at {d} and the bucket holds no key for it"));
            }
        }
    }
    for key in world.inner.list("sched/", usize::MAX).await.unwrap_or_default() {
        let Ok(Some((bytes, _))) = world.inner.get(&key).await else { continue };
        let rows = echod_logic::doc::decode::<echod_kernel::Schedule>(&bytes).map(|l| l.rows).unwrap_or_default();
        let id = key.trim_start_matches("sched/");
        let id = echod_logic::keys::decode_key(id).unwrap_or_else(|| id.to_string());
        if let Some(d) = echod_kernel::steps::next_deadline(&echod_kernel::State { objects: Vec::new(), schedules: rows, outbox: Vec::new() }) {
            if !armed.contains(&(format!("sched:{id}"), d)) {
                report.failures.push(format!("schedule {id}: owes its next run at {d} and the bucket holds no key for it"));
            }
        }
    }

    report.ok = report.failures.is_empty();
    report
}
