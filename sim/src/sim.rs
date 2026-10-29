//! The run: nodes over one store, clients, crashes, then the checks.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use echod::env::{Clock, Notes};
use echod::store::{MemoryStore, Store};
use echod::{Config, Node as Server};
use echod_logic::keys::{KeySpace, TimerEntry};
use echod_logic::Note;
use resonate_core::types::{RequestEnvelope, RequestHead, PROTOCOL_VERSION};
use resonate_core::ResonateServer;
use serde::Serialize;

use resonate::Request;

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
    /// Whether clients touch schedules (`--schedules`).
    pub schedules: bool,
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
    /// Requests sent to a node other than the origin's owner, in percent.
    pub misroute_percent: u64,
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

impl Options {
    /// How long after its instant a schedule's occurrence is owed, for the
    /// checker: a node gets to a deadline when its wheel reaches it, and to one
    /// another node armed when it lists the bucket, so within a bucket or two,
    /// as its clock reads them.
    pub fn fire_within(&self) -> u64 {
        2 * self.timer_bucket_ms + 2 * self.skew_ms + self.jump_ms
    }
}

impl Default for Options {
    fn default() -> Self {
        Self {
            seed: 1,
            servers: 2,
            clients: 3,
            operations: 200,
            // as the command line: three clients over six origins; over three,
            // the in-flight writes on one origin widen the checker's profile
            origins: 6,
            promises_per_origin: 3,
            schedules: false,
            faults: Faults { unavailable_percent: 2, lost_ack_percent: 2, conflict_percent: 2, latency_ms: 20 },
            crash_percent: 10,
            stop_percent: 5,
            join_percent: 8,
            outage_percent: 10,
            jump_percent: 15,
            misroute_percent: 0,
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
    /// Events in the checker's trace.
    pub events: usize,
    /// Nodes the checker explored.
    pub search_steps: u64,
    pub failures: Vec<String>,
}

/// The nodes' own steps enter the history through the notes port: the
/// instant each was decided at is a clock move the checker must know of
/// (a document's stamp may rest on it), and the sweeps and fires are counted.
struct StepNotes {
    history: Arc<History>,
    sweeps: AtomicU64,
    fires: AtomicU64,
}

impl Notes for StepNotes {
    fn note(&self, _node: &str, n: &Note) {
        match n {
            Note::SweepBegin { now, .. } => {
                self.history.mark(*now);
                self.sweeps.fetch_add(1, Ordering::Relaxed);
            }
            Note::FireBegin { now, .. } => {
                self.history.mark(*now);
                self.fires.fetch_add(1, Ordering::Relaxed);
            }
            Note::AdvanceBegin { now, .. } => self.history.mark(*now),
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
        let store: Arc<dyn Store> = Arc::clone(&node_store) as Arc<dyn Store>;
        let server = Server::with_env(cfg, store, Arc::clone(&self.bus) as Arc<dyn resonate_core::ResonateRouter>, Arc::clone(&clock) as Arc<dyn Clock>, Arc::clone(&self.notes) as Arc<dyn Notes>);
        // Deliver core timer intents on paused Tokio time; the simulation
        // controls when virtual time reaches each versioned completion.
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
        // As a load balancer over the members would: the origin's owner,
        // which serialises the origin's requests behind one flight. A
        // misrouted request is served by any node, after revalidating its
        // cache; a read there may miss a write the owner has decided and
        // not yet landed, whose stamp precedes the read, which the model's
        // one clock cannot show.
        let i = if rng.percent(self.opts.misroute_percent) { rng.below(live.len() as u64) as usize } else { (echod_logic::keys::fnv1a(origin) % live.len() as u64) as usize };
        Some(Arc::clone(&live[i].server))
    }

    async fn client(self: Arc<Self>, name: String, mut rng: Rng) {
        let gen = Generator { origins: self.opts.origins, promises_per_origin: self.opts.promises_per_origin, schedules: self.opts.schedules, timeout_ms: self.opts.timeout_ms, ttl_ms: self.opts.ttl_ms };
        let mut seen = Seen::default();
        while self.issued.fetch_add(1, Ordering::Relaxed) < self.opts.operations {
            let now = self.clock.now();
            let req = gen.next(&mut rng, &seen, now);
            if let Some(data) = self.issue(&name, req, &mut rng).await {
                seen.note(&data);
            }
            tokio::time::sleep(Duration::from_millis(rng.range(0, self.opts.think_ms))).await;
        }
    }

    /// One request, retried until answered, backing off as a client does (a
    /// node cut off from the store answers nothing useful for seconds, and
    /// every attempt in that time is one more call the checker must place).
    /// Every attempt is its own entry at the injected clock's current
    /// instant: one that got no answer may have taken effect, and a retry of
    /// it is not the same operation again (an acquire retried after a lost
    /// answer is refused). The answer's data, if one came.
    async fn issue(&self, name: &str, req: Request, rng: &mut Rng) -> Option<serde_json::Value> {
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
            let now = self.clock.now();
            let entry = self.history.begin(name, req.clone(), now, now);
            self.history.attempt(entry);
            let envelope = RequestEnvelope {
                kind: kind.to_string(),
                head: RequestHead { corr_id: format!("c{entry}"), version: PROTOCOL_VERSION.to_string(), auth: None, debug_time: None },
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
                    if attempts >= 30 {
                        return None;
                    }
                    // 50 ms, doubling to a second, with jitter
                    let base = (50u64 << (attempts - 1).min(5)).min(1_000);
                    tokio::time::sleep(Duration::from_millis(base + rng.range(1, 50))).await;
                }
            }
        }
    }

    /// The finishing reads: every id the run may have named, read once the
    /// run has settled, so what the bucket holds is what the model shows.
    async fn final_reads(&self, rng: &mut Rng) {
        let gen = Generator { origins: self.opts.origins, promises_per_origin: self.opts.promises_per_origin, schedules: self.opts.schedules, timeout_ms: self.opts.timeout_ms, ttl_ms: self.opts.ttl_ms };
        let mut reads = Vec::new();
        for id in gen.ids() {
            reads.push(Request::GetPromise(id.clone()));
            reads.push(Request::GetTask(id));
        }
        if self.opts.schedules {
            for id in SCHEDULES {
                reads.push(Request::GetSchedule(id.to_string()));
            }
        }
        for req in reads {
            self.issue("final", req, rng).await;
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
        notes: Arc::new(StepNotes { history, sweeps: AtomicU64::new(0), fires: AtomicU64::new(0) }),
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
    let trace = checker::trace(&entries, &world.history.marks(), &sent);
    report.events = trace.len();
    match checker::check(&trace, opts.retry_timeout_ms, opts.fire_within(), opts.budget) {
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
