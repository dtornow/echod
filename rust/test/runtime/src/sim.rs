//! A purely synchronous deterministic system around the production core.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use echod_abstract_spec::Dispatch;
use echod_logic::types::{Answer, Armed, Effect, Event, StoreCall};
use echod_logic::{Call, Config, Message, Note, State, Target};
use echod_types::{PromiseGetReq, PromiseState, Request, Response, ScheduleGetReq, TaskGetReq};
use serde::Serialize;

use crate::checker::{self, Verdict};
use crate::history::History;
use crate::rng::Rng;
use crate::store::{Counters, Disposition, Faults, FaultyStore};
use crate::workload::{target_of, Generator, Seen, SCHEDULES};

const START_MS: u64 = 1_700_000_000_000;

#[derive(Clone, Debug)]
pub struct Options {
    pub seed: u64,
    pub servers: u32,
    pub clients: u32,
    pub operations: u64,
    pub origins: u64,
    pub promises_per_origin: u64,
    pub schedules: bool,
    pub faults: Faults,
    pub crash_percent: u64,
    pub stop_percent: u64,
    pub join_percent: u64,
    pub outage_percent: u64,
    pub jump_percent: u64,
    pub misroute_percent: u64,
    pub chaos_every_ms: u64,
    pub disruption_ms: u64,
    pub skew_ms: u64,
    pub drift_ppm: u64,
    pub jump_ms: u64,
    pub max_servers: u32,
    pub timeout_ms: u64,
    pub ttl_ms: u64,
    pub retry_timeout_ms: u64,
    pub timer_bucket_ms: u64,
    pub heartbeat_ms: u64,
    pub node_ttl_ms: u64,
    pub think_ms: u64,
    pub settle_ms: u64,
    pub budget: u64,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            seed: 1,
            servers: 2,
            clients: 3,
            operations: 200,
            origins: 6,
            promises_per_origin: 3,
            schedules: false,
            faults: Faults {
                unavailable_percent: 2,
                lost_ack_percent: 2,
                conflict_percent: 2,
                latency_ms: 20,
            },
            crash_percent: 10,
            stop_percent: 5,
            join_percent: 8,
            outage_percent: 10,
            jump_percent: 15,
            misroute_percent: 0,
            chaos_every_ms: 500,
            disruption_ms: 2_500,
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
    pub events: usize,
    pub search_steps: u64,
    pub undecided: bool,
    pub failures: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Sent {
    pub at: u64,
    pub address: String,
    pub kind: String,
    pub id: String,
    pub msg: Dispatch,
}

struct Node {
    state: State,
    skew_ms: i64,
    drift_ppm: i64,
    offset_ms: i64,
    band_ms: i64,
    cut: bool,
    outage_token: u64,
    wake_token: u64,
    routable: bool,
}

impl Node {
    fn clock(&self, reference: u64) -> u64 {
        let elapsed = reference.saturating_sub(START_MS) as i64;
        let drift = elapsed.saturating_mul(self.drift_ppm) / 1_000_000;
        (reference as i64 + self.skew_ms + drift + self.offset_ms).max(0) as u64
    }
}

struct Active {
    req: Request,
    attempts: u32,
}

struct Client {
    name: String,
    rng: Rng,
    seen: Seen,
    active: Option<Active>,
    planned: VecDeque<Request>,
    generated: bool,
}

struct Pending {
    client: usize,
    node: String,
}

enum SystemEvent {
    Store {
        node: String,
        op: u64,
        call: StoreCall,
        disposition: Disposition,
    },
    Wake {
        node: String,
        token: u64,
        armed: Armed,
    },
    ClientReady(usize),
    Retry(usize),
    Chaos,
    Heal {
        node: String,
        token: u64,
    },
}

struct World {
    opts: Options,
    now: u64,
    appendable: bool,
    store: FaultyStore,
    nodes: BTreeMap<String, Node>,
    next_node: u32,
    queue: BTreeMap<(u64, u64), SystemEvent>,
    sequence: u64,
    clients: Vec<Client>,
    generated_clients: usize,
    issued: u64,
    pending: BTreeMap<u64, Pending>,
    history: History,
    sent: Vec<Sent>,
    chaos_rng: Rng,
    crashes: u32,
    stops: u32,
    joins: u32,
    outages: u32,
    jumps: u32,
    sweeps: usize,
    fires: usize,
    executes: u64,
    unblocks: u64,
    message_violations: Vec<String>,
}

impl World {
    fn new(opts: Options) -> Self {
        let mut rng = Rng::new(opts.seed);
        let appendable = rng.percent(50);
        let store_rng = rng.fork();
        let chaos_rng = rng.fork();
        Self {
            store: FaultyStore::new(appendable, opts.faults, store_rng),
            opts,
            now: START_MS,
            appendable,
            nodes: BTreeMap::new(),
            next_node: 0,
            queue: BTreeMap::new(),
            sequence: 0,
            clients: Vec::new(),
            generated_clients: 0,
            issued: 0,
            pending: BTreeMap::new(),
            history: History::new(),
            sent: Vec::new(),
            chaos_rng,
            crashes: 0,
            stops: 0,
            joins: 0,
            outages: 0,
            jumps: 0,
            sweeps: 0,
            fires: 0,
            executes: 0,
            unblocks: 0,
            message_violations: Vec::new(),
        }
    }

    fn schedule(&mut self, at: u64, event: SystemEvent) {
        let key = (at, self.sequence);
        self.sequence = self.sequence.wrapping_add(1);
        self.queue.insert(key, event);
    }

    fn pop(&mut self) -> Option<(u64, SystemEvent)> {
        let key = *self.queue.keys().next()?;
        let event = self.queue.remove(&key)?;
        Some((key.0, event))
    }

    fn node_clock(&self, id: &str) -> Option<u64> {
        self.nodes.get(id).map(|node| node.clock(self.now))
    }

    fn start_node(&mut self, rng: &mut Rng) {
        self.next_node += 1;
        let id = format!("s{}", self.next_node);
        let skew =
            rng.range(0, self.opts.skew_ms.saturating_mul(2)) as i64 - self.opts.skew_ms as i64;
        let drift =
            rng.range(0, self.opts.drift_ppm.saturating_mul(2)) as i64 - self.opts.drift_ppm as i64;
        let mut cfg = Config::memory(&id);
        cfg.url = format!("sim://{id}/");
        cfg.compact = if self.appendable { 8 } else { 0 };
        cfg.appendable = self.appendable;
        cfg.retry_timeout = self.opts.retry_timeout_ms;
        cfg.timer_bucket_ms = self.opts.timer_bucket_ms;
        cfg.heartbeat_ms = self.opts.heartbeat_ms;
        cfg.node_ttl_ms = self.opts.node_ttl_ms;
        cfg.debug = true;
        let node = Node {
            state: State::new(cfg),
            skew_ms: skew,
            drift_ppm: drift,
            offset_ms: 0,
            band_ms: self.opts.jump_ms as i64,
            cut: false,
            outage_token: 0,
            wake_token: 0,
            routable: true,
        };
        let clock = node.clock(self.now);
        self.nodes.insert(id.clone(), node);
        self.apply_node(&id, Event::Start { clock, loops: true });
    }

    fn apply_node(&mut self, id: &str, event: Event) {
        let effects = match self.nodes.get_mut(id) {
            Some(node) => node.state.on_event(event),
            None => return,
        };
        self.perform(id, effects);
        if self.nodes.get(id).is_some_and(|node| node.state.stopped()) {
            self.remove_node(id);
        }
    }

    fn perform(&mut self, id: &str, effects: Vec<Effect>) {
        for effect in effects {
            match effect {
                Effect::Store { op, call } => {
                    let cut = self.nodes.get(id).is_none_or(|node| node.cut);
                    let (delay, disposition) = if cut {
                        (0, Disposition::Unavailable)
                    } else {
                        self.store.plan(&call)
                    };
                    self.schedule(
                        self.now.saturating_add(delay),
                        SystemEvent::Store {
                            node: id.to_string(),
                            op,
                            call,
                            disposition,
                        },
                    );
                }
                Effect::Reply {
                    id: request,
                    response,
                } => {
                    self.reply(request, response);
                }
                Effect::Send { address, message } => self.send(address, message),
                Effect::Wake { after_ms, armed } => {
                    if let Some(node) = self.nodes.get_mut(id) {
                        node.wake_token = node.wake_token.wrapping_add(1);
                        let token = node.wake_token;
                        self.schedule(
                            self.now.saturating_add(after_ms),
                            SystemEvent::Wake {
                                node: id.to_string(),
                                token,
                                armed,
                            },
                        );
                    }
                }
                Effect::Note(note) => self.note(note),
            }
        }
    }

    fn note(&mut self, note: Note) {
        match note {
            Note::SweepBegin { now, .. } => {
                self.sweeps += 1;
                self.history.mark(now);
            }
            Note::FireBegin { now, .. } => {
                self.fires += 1;
                self.history.mark(now);
            }
            Note::AdvanceBegin { now, .. } => self.history.mark(now),
            _ => {}
        }
    }

    fn send(&mut self, address: String, message: Message) {
        let at = self.now;
        let (kind, id, msg) = match &message {
            Message::Execute { task_id, version } => {
                self.executes += 1;
                let rows = self.rows(echod_types::origin_of(task_id));
                if !rows
                    .iter()
                    .any(|promise| promise.id == *task_id && promise.task.is_some())
                {
                    self.message_violations.push(format!(
                        "execute for {task_id} at {at}: no such task in the bucket"
                    ));
                }
                (
                    "execute",
                    task_id.clone(),
                    Dispatch::Execute {
                        id: task_id.clone(),
                        version: *version,
                    },
                )
            }
            Message::Unblock(promise) => {
                self.unblocks += 1;
                let rows = self.rows(echod_types::origin_of(&promise.id));
                let settled = rows
                    .iter()
                    .find(|row| row.id == promise.id)
                    .is_some_and(|row| row.state != PromiseState::Pending || row.timeout_at <= at);
                if !settled {
                    self.message_violations.push(format!(
                        "unblock for {} at {at}: the promise is not settled in the bucket",
                        promise.id
                    ));
                }
                if promise.state == PromiseState::Pending {
                    self.message_violations.push(format!(
                        "unblock for {} at {at}: carries a pending promise",
                        promise.id
                    ));
                }
                (
                    "unblock",
                    promise.id.clone(),
                    Dispatch::Unblock {
                        address: address.clone(),
                        promise: promise.clone(),
                    },
                )
            }
        };
        self.sent.push(Sent {
            at,
            address,
            kind: kind.into(),
            id,
            msg,
        });
    }

    fn rows(&self, origin: &str) -> Vec<echod_logic::doc::codec::Promise> {
        let key = echod_logic::keys::KeySpace::new("", self.opts.timer_bucket_ms).doc_key(origin);
        self.store
            .get(&key)
            .and_then(|bytes| echod_logic::doc::decode_origin(bytes).ok())
            .map(|loaded| echod_logic::doc::codec::promises(&loaded.doc))
            .unwrap_or_default()
    }

    fn reply(&mut self, request: u64, answer: Result<Answer, String>) {
        let Some(pending) = self.pending.remove(&request) else {
            return;
        };
        match answer {
            Ok(Answer::Step { response, .. }) => {
                self.history.end(request, self.now, Some(response.clone()));
                if let Some(client) = self.clients.get_mut(pending.client) {
                    client.seen.note(&response);
                    client.active = None;
                }
                self.ready_after(pending.client);
            }
            Ok(Answer::Debug { .. }) | Err(_) => {
                self.history.end(request, self.now, None);
                self.retry_or_finish(pending.client);
            }
        }
    }

    fn ready_after(&mut self, client: usize) {
        let delay = if client < self.generated_clients {
            self.clients[client].rng.range(0, self.opts.think_ms)
        } else {
            0
        };
        self.schedule(
            self.now.saturating_add(delay),
            SystemEvent::ClientReady(client),
        );
    }

    fn retry_or_finish(&mut self, client: usize) {
        let Some(active) = self.clients.get(client).and_then(|c| c.active.as_ref()) else {
            return;
        };
        if active.attempts >= 30 {
            self.clients[client].active = None;
            self.ready_after(client);
            return;
        }
        let attempts = active.attempts;
        let base = (50u64 << attempts.saturating_sub(1).min(5)).min(1_000);
        let jitter = self.clients[client].rng.range(1, 50);
        self.schedule(
            self.now.saturating_add(base).saturating_add(jitter),
            SystemEvent::Retry(client),
        );
    }

    fn client_ready(&mut self, client: usize) {
        if self.clients.get(client).is_none() || self.clients[client].active.is_some() {
            return;
        }
        let req = if let Some(req) = self.clients[client].planned.pop_front() {
            Some(req)
        } else if self.clients[client].generated && self.issued < self.opts.operations {
            self.issued += 1;
            let generator = Generator {
                origins: self.opts.origins,
                promises_per_origin: self.opts.promises_per_origin,
                schedules: self.opts.schedules,
                timeout_ms: self.opts.timeout_ms,
                ttl_ms: self.opts.ttl_ms,
            };
            let client = &mut self.clients[client];
            Some(generator.next(&mut client.rng, &client.seen, self.now))
        } else {
            None
        };
        if let Some(req) = req {
            self.clients[client].active = Some(Active { req, attempts: 0 });
            self.attempt(client);
        }
    }

    fn attempt(&mut self, client: usize) {
        let Some(active) = self.clients.get_mut(client).and_then(|c| c.active.as_mut()) else {
            return;
        };
        active.attempts += 1;
        let req = active.req.clone();
        let target = target_of(&req);
        let ids: Vec<String> = self
            .nodes
            .iter()
            .filter(|(_, node)| node.routable)
            .map(|(id, _)| id.clone())
            .collect();
        if ids.is_empty() {
            if active.attempts >= 200 {
                self.clients[client].active = None;
                self.ready_after(client);
            } else {
                self.schedule(self.now.saturating_add(50), SystemEvent::Retry(client));
            }
            return;
        }
        let index = if self.clients[client].rng.percent(self.opts.misroute_percent) {
            self.clients[client].rng.below(ids.len() as u64) as usize
        } else {
            (echod_logic::keys::fnv1a(&target) % ids.len() as u64) as usize
        };
        let node = ids[index].clone();
        let entry = self
            .history
            .begin(&self.clients[client].name, req.clone(), self.now, self.now);
        self.history.attempt(entry);
        self.pending.insert(
            entry,
            Pending {
                client,
                node: node.clone(),
            },
        );
        let call = Call {
            id: entry,
            kind: kind_of(&req).into(),
            corr: format!("c{entry}"),
            target: Target::of_name(&target),
            action_kind: action_kind(&req).map(str::to_string),
            request: req,
            now: self.now,
            pinned: true,
            then: None,
        };
        let clock = self.node_clock(&node).unwrap_or(self.now);
        self.apply_node(&node, Event::Request { clock, call });
    }

    fn remove_node(&mut self, id: &str) {
        if self.nodes.remove(id).is_none() {
            return;
        }
        let requests: Vec<u64> = self
            .pending
            .iter()
            .filter(|(_, pending)| pending.node == id)
            .map(|(request, _)| *request)
            .collect();
        for request in requests {
            if let Some(pending) = self.pending.remove(&request) {
                self.history.end(request, self.now, None);
                self.retry_or_finish(pending.client);
            }
        }
    }

    fn routable_ids(&self) -> Vec<String> {
        self.nodes
            .iter()
            .filter(|(_, node)| node.routable)
            .map(|(id, _)| id.clone())
            .collect()
    }

    fn chaos(&mut self) {
        if self.issued >= self.opts.operations {
            return;
        }
        let mut rng = std::mem::replace(&mut self.chaos_rng, Rng::new(0));
        let crash = rng.percent(self.opts.crash_percent);
        let stop = rng.percent(self.opts.stop_percent);
        let join = rng.percent(self.opts.join_percent);
        let outage = rng.percent(self.opts.outage_percent);
        let jump = rng.percent(self.opts.jump_percent);
        if crash {
            self.crash_one(&mut rng);
        }
        if stop {
            self.stop_one(&mut rng);
        }
        if join {
            self.join_one(&mut rng);
        }
        if outage {
            self.outage_one(&mut rng);
        }
        if jump {
            self.jump_one(&mut rng);
        }
        self.chaos_rng = rng;
        self.schedule(
            self.now.saturating_add(self.opts.chaos_every_ms.max(1)),
            SystemEvent::Chaos,
        );
    }

    fn picked(&self, rng: &mut Rng) -> Option<String> {
        let ids = self.routable_ids();
        (!ids.is_empty()).then(|| rng.pick(&ids).clone())
    }

    fn crash_one(&mut self, rng: &mut Rng) {
        let Some(id) = self.picked(rng) else { return };
        self.remove_node(&id);
        self.crashes += 1;
        self.start_node(rng);
    }

    fn stop_one(&mut self, rng: &mut Rng) {
        if self.routable_ids().len() <= 1 {
            return;
        }
        let Some(id) = self.picked(rng) else { return };
        if let Some(node) = self.nodes.get_mut(&id) {
            node.routable = false;
        }
        self.stops += 1;
        let clock = self.node_clock(&id).unwrap_or(self.now);
        self.apply_node(&id, Event::Stop { clock });
    }

    fn join_one(&mut self, rng: &mut Rng) {
        if self.routable_ids().len() as u32 >= self.opts.max_servers {
            return;
        }
        self.start_node(rng);
        self.joins += 1;
    }

    fn outage_one(&mut self, rng: &mut Rng) {
        let Some(id) = self.picked(rng) else { return };
        let duration = rng.range(100, self.opts.disruption_ms);
        let token = {
            let node = self.nodes.get_mut(&id).expect("picked node");
            node.cut = true;
            node.outage_token = node.outage_token.wrapping_add(1);
            node.outage_token
        };
        self.outages += 1;
        self.schedule(
            self.now.saturating_add(duration),
            SystemEvent::Heal { node: id, token },
        );
    }

    fn jump_one(&mut self, rng: &mut Rng) {
        let Some(id) = self.picked(rng) else { return };
        let delta =
            rng.range(0, self.opts.jump_ms.saturating_mul(2)) as i64 - self.opts.jump_ms as i64;
        if let Some(node) = self.nodes.get_mut(&id) {
            node.offset_ms = (node.offset_ms + delta).clamp(-node.band_ms, node.band_ms);
        }
        self.jumps += 1;
    }

    fn step(&mut self, event: SystemEvent) {
        match event {
            SystemEvent::Store {
                node,
                op,
                call,
                disposition,
            } => {
                if !self.nodes.contains_key(&node) {
                    return;
                }
                let outcome = self.store.complete(&call, disposition);
                let clock = self.node_clock(&node).unwrap_or(self.now);
                self.apply_node(&node, Event::Completed { op, outcome, clock });
            }
            SystemEvent::Wake { node, token, armed } => {
                let valid = self
                    .nodes
                    .get(&node)
                    .is_some_and(|state| state.wake_token == token);
                if !valid {
                    return;
                }
                if let Some(state) = self.nodes.get_mut(&node) {
                    state.wake_token = state.wake_token.wrapping_add(1);
                }
                let clock = self.node_clock(&node).unwrap_or(self.now);
                self.apply_node(&node, Event::Due { clock, armed });
            }
            SystemEvent::ClientReady(client) => self.client_ready(client),
            SystemEvent::Retry(client) => self.attempt(client),
            SystemEvent::Chaos => self.chaos(),
            SystemEvent::Heal { node, token } => {
                if let Some(state) = self.nodes.get_mut(&node) {
                    if state.outage_token == token {
                        state.cut = false;
                    }
                }
            }
        }
    }

    fn next_event(&mut self) -> bool {
        let Some((at, event)) = self.pop() else {
            return false;
        };
        self.now = self.now.max(at);
        self.step(event);
        true
    }

    fn run_until(&mut self, mut done: impl FnMut(&Self) -> bool) {
        while !done(self) {
            assert!(self.next_event(), "deterministic event queue drained");
        }
    }

    fn run_through(&mut self, through: u64) {
        while self
            .queue
            .keys()
            .next()
            .is_some_and(|(at, _)| *at <= through)
        {
            self.next_event();
        }
        self.now = self.now.max(through);
    }

    fn normal_done(&self) -> bool {
        self.issued >= self.opts.operations
            && self.clients[..self.generated_clients]
                .iter()
                .all(|client| client.active.is_none())
    }

    fn heal_all(&mut self) {
        for node in self.nodes.values_mut() {
            node.cut = false;
            node.outage_token = node.outage_token.wrapping_add(1);
        }
    }

    fn add_final_client(&mut self) -> usize {
        let generator = Generator {
            origins: self.opts.origins,
            promises_per_origin: self.opts.promises_per_origin,
            schedules: self.opts.schedules,
            timeout_ms: self.opts.timeout_ms,
            ttl_ms: self.opts.ttl_ms,
        };
        let mut planned = VecDeque::new();
        for id in generator.ids() {
            planned.push_back(Request::PromiseGet(PromiseGetReq { id: id.clone() }));
            planned.push_back(Request::TaskGet(TaskGetReq { id }));
        }
        if self.opts.schedules {
            for id in SCHEDULES {
                planned.push_back(Request::ScheduleGet(ScheduleGetReq { id: id.into() }));
            }
        }
        let index = self.clients.len();
        self.clients.push(Client {
            name: "final".into(),
            rng: Rng::new(self.opts.seed ^ 0xf1a1),
            seen: Seen::default(),
            active: None,
            planned,
            generated: false,
        });
        self.schedule(self.now, SystemEvent::ClientReady(index));
        index
    }

    fn final_done(&self, client: usize) -> bool {
        self.clients[client].active.is_none() && self.clients[client].planned.is_empty()
    }

    fn stop_all(&mut self) {
        let ids = self.routable_ids();
        for id in ids {
            if let Some(node) = self.nodes.get_mut(&id) {
                node.routable = false;
            }
            let clock = self.node_clock(&id).unwrap_or(self.now);
            self.apply_node(&id, Event::Stop { clock });
        }
        self.run_until(|world| world.nodes.is_empty());
    }
}

pub fn run(opts: Options) -> Report {
    let mut world = World::new(opts.clone());
    let mut startup_rng = Rng::new(opts.seed ^ 0x51a7);
    for _ in 0..opts.servers {
        world.start_node(&mut startup_rng);
    }
    world.run_through(
        world
            .now
            .saturating_add(opts.node_ttl_ms)
            .saturating_add(opts.heartbeat_ms.saturating_mul(4)),
    );

    let mut client_rng = Rng::new(opts.seed ^ 0xc11e_17);
    for index in 0..opts.clients as usize {
        world.clients.push(Client {
            name: format!("client{index}"),
            rng: client_rng.fork(),
            seen: Seen::default(),
            active: None,
            planned: VecDeque::new(),
            generated: true,
        });
    }
    world.generated_clients = world.clients.len();
    for client in 0..world.generated_clients {
        world.schedule(world.now, SystemEvent::ClientReady(client));
    }
    world.schedule(
        world.now.saturating_add(opts.chaos_every_ms.max(1)),
        SystemEvent::Chaos,
    );
    world.run_until(World::normal_done);

    world.heal_all();
    if world.routable_ids().is_empty() {
        world.start_node(&mut startup_rng);
    }
    world.run_through(world.now.saturating_add(opts.settle_ms));
    let final_client = world.add_final_client();
    world.run_until(|state| state.final_done(final_client));
    world.stop_all();
    world.history.close_open(world.now);
    check(&world)
}

fn check(world: &World) -> Report {
    let entries = world.history.entries();
    let mut report = Report {
        seed: world.opts.seed,
        entries: entries.len(),
        sweeps: world.sweeps,
        fires: world.fires,
        crashes: world.crashes,
        stops: world.stops,
        joins: world.joins,
        outages: world.outages,
        jumps: world.jumps,
        executes: world.executes,
        unblocks: world.unblocks,
        ..Default::default()
    };
    let counters: Counters = world.store.counters();
    report.store_operations = counters.operations;
    report.store_unavailable = counters.unavailable;
    report.store_lost_acks = counters.lost_acks;
    report.store_conflicts = counters.conflicts;
    for violation in &world.message_violations {
        report.failures.push(format!("message: {violation}"));
    }

    let all_kinds: BTreeSet<String> = [
        "promise.get",
        "promise.create",
        "promise.settle",
        "promise.register_callback",
        "promise.register_listener",
        "task.get",
        "task.create",
        "task.acquire",
        "task.fulfill",
        "task.release",
        "task.heartbeat",
        "task.suspend",
        "task.fence",
        "task.halt",
        "task.continue",
        "schedule.get",
        "schedule.create",
        "schedule.delete",
    ]
    .iter()
    .map(|kind| kind.to_string())
    .collect();
    for entry in &entries {
        if entry
            .outcome
            .as_ref()
            .is_some_and(|response| status(response) == 200)
        {
            report.kinds_succeeded.insert(kind_of(&entry.req).into());
        }
    }
    report.kinds_missing = all_kinds
        .difference(&report.kinds_succeeded)
        .cloned()
        .collect();
    let clients: Vec<_> = entries
        .iter()
        .filter(|entry| entry.client != "final")
        .collect();
    for (index, a) in clients.iter().enumerate() {
        for b in &clients[index + 1..] {
            if b.invoke < a.ret && a.invoke <= b.invoke {
                report.overlapping_pairs += 1;
            }
        }
    }
    if report.overlapping_pairs == 0 && world.opts.clients > 1 {
        report
            .failures
            .push("the history never overlapped: nothing concurrent was checked".into());
    }

    let trace = checker::trace(&entries, &world.history.marks(), &world.sent);
    report.events = trace.len();
    match checker::check(&trace, world.opts.retry_timeout_ms, world.opts.budget) {
        Verdict::Ok { explored } => report.search_steps = explored as u64,
        Verdict::Unknown(violation) => {
            report.undecided = true;
            if std::env::var_os("ECHOD_SIM_DUMP").is_some() {
                eprintln!(
                    "undecided at event {} of {}: {}",
                    violation.index,
                    trace.len(),
                    violation.reason
                );
                eprint!("{}", checker::show(&trace, violation.index));
            }
        }
    }

    validate_deadlines(world, &mut report);
    report.ok = report.failures.is_empty();
    report
}

fn validate_deadlines(world: &World, report: &mut Report) {
    let keys = echod_logic::keys::KeySpace::new("", world.opts.timer_bucket_ms);
    let armed: BTreeSet<(String, u64)> = world
        .store
        .list("t/")
        .iter()
        .filter_map(|key| match keys.parse_timer_key(key) {
            Some(echod_logic::keys::TimerEntry::Origin {
                origin, deadline, ..
            }) => Some((origin, deadline)),
            Some(echod_logic::keys::TimerEntry::Schedule { id, deadline, .. }) => {
                Some((format!("sched:{id}"), deadline))
            }
            None => None,
        })
        .collect();
    for key in world.store.list("wf/") {
        let Some(bytes) = world.store.get(&key) else {
            continue;
        };
        let Ok(loaded) = echod_logic::doc::decode_origin(bytes) else {
            continue;
        };
        let encoded = key.trim_start_matches("wf/");
        let origin = echod_logic::keys::decode_key(encoded).unwrap_or_else(|| encoded.to_string());
        if let Some(deadline) = echod_logic::doc::deadline(&loaded.doc) {
            if !armed.contains(&(origin.clone(), deadline)) {
                report.failures.push(format!(
                    "origin {origin}: owes a deadline at {deadline} and the bucket holds no key for it"
                ));
            }
        }
    }
    for key in world.store.list("sched/") {
        let Some(bytes) = world.store.get(&key) else {
            continue;
        };
        let Ok(loaded) = echod_logic::doc::decode_schedule(bytes) else {
            continue;
        };
        let encoded = key.trim_start_matches("sched/");
        let id = echod_logic::keys::decode_key(encoded).unwrap_or_else(|| encoded.to_string());
        if let Some(deadline) = echod_logic::doc::deadline(&loaded.doc) {
            if !armed.contains(&(format!("sched:{id}"), deadline)) {
                report.failures.push(format!(
                    "schedule {id}: owes its next run at {deadline} and the bucket holds no key for it"
                ));
            }
        }
    }
}

fn status(response: &Response) -> u16 {
    match response {
        Response::Promise(response) => response.status,
        Response::Schedule(response) => response.status,
        Response::Status(response) => response.status,
        Response::TaskGet(response) => response.status,
        Response::TaskClaim(response) => response.status,
        Response::TaskFence(response) => response.status,
    }
}

fn action_kind(request: &Request) -> Option<&'static str> {
    match request {
        Request::TaskFence(fence) => Some(match &fence.action {
            echod_types::TaskFenceAction::Create(_) => "promise.create",
            echod_types::TaskFenceAction::Settle(_) => "promise.settle",
        }),
        _ => None,
    }
}

pub fn kind_of(request: &Request) -> &'static str {
    match request {
        Request::PromiseGet(_) => "promise.get",
        Request::PromiseCreate(_) => "promise.create",
        Request::PromiseSettle(_) => "promise.settle",
        Request::PromiseRegisterCallback(_) => "promise.register_callback",
        Request::PromiseRegisterListener(_) => "promise.register_listener",
        Request::ScheduleGet(_) => "schedule.get",
        Request::ScheduleCreate(_) => "schedule.create",
        Request::ScheduleDelete(_) => "schedule.delete",
        Request::TaskGet(_) => "task.get",
        Request::TaskCreate(_) => "task.create",
        Request::TaskAcquire(_) => "task.acquire",
        Request::TaskFulfill(_) => "task.fulfill",
        Request::TaskRelease(_) => "task.release",
        Request::TaskHalt(_) => "task.halt",
        Request::TaskContinue(_) => "task.continue",
        Request::TaskFence(_) | Request::TaskFenceCheck(_) => "task.fence",
        Request::TaskHeartbeat(_) => "task.heartbeat",
        Request::TaskSuspend(_) => "task.suspend",
    }
}
