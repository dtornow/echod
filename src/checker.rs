use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::intern::{Interned, Interner};
use crate::{CallId, Fairness, Keys, Sched, Spec, StepResult, Time};

/// Work a node still carries. Sorted, so a node's identity is canonical.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Pending<O, R, T> {
    /// Invoked at `since`, not yet linearized. It may take effect at any point
    /// until its `Return`, or never if no `Return` comes. `must`: this branch has
    /// committed to it taking effect before its request lifetime ends.
    InFlight { call: CallId, op: O, since: Time, must: bool },
    /// Linearized; the spec predicted `resp`, which the `Return` must match.
    Responded { call: CallId, resp: R },
    /// Background work, due from `after`. `must`: owed by `by`, or by the next
    /// `Quiesce` if `by` is `None`.
    Step { step: T, after: Time, by: Option<Time>, must: bool },
}

type P<S> = Pending<<S as Spec>::Op, <S as Spec>::Resp, <S as Spec>::Step>;

/// One explanation of the history so far.
pub struct Node<S: Spec> {
    pub state: Interned<S::State>,
    pub pending: BTreeSet<P<S>>,
}

impl<S: Spec> Clone for Node<S> {
    fn clone(&self) -> Self {
        Node { state: self.state.clone(), pending: self.pending.clone() }
    }
}

impl<S: Spec> PartialEq for Node<S> {
    fn eq(&self, other: &Self) -> bool {
        self.pending == other.pending && self.state == other.state
    }
}

impl<S: Spec> Eq for Node<S> {}

impl<S: Spec> Hash for Node<S> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.state.hash(h);
        self.pending.hash(h);
    }
}

impl<S: Spec> fmt::Debug for Node<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node").field("state", &self.state).field("pending", &self.pending).finish()
    }
}

/// Everything happens at the checker's current time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event<O, R> {
    Invoke(CallId, O),
    Return(CallId, R),
    /// Time advances to the given instant. The checker stops at every timer and
    /// deadline on the way, so work fires at the instant it is due.
    Tick(Time),
    /// The system is idle: every obligation that is due has fired. Calls still
    /// awaiting a response are untouched.
    Quiesce,
}

#[derive(Clone, Debug)]
pub struct Config {
    /// An unanswered request takes effect within this long of its invoke, or never.
    /// `None`: it may take effect at any time.
    pub request_lifetime: Option<Time>,
    /// Prune work whose footprint is disjoint from what an observation needs.
    pub footprints: bool,
    /// Drop nodes another node can simulate (it carries a superset of optional work).
    pub subsume: bool,
    /// Fail rather than let the profile grow past this.
    pub max_width: usize,
    /// Fail rather than explore more nodes than this for one event.
    pub max_explore: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config { request_lifetime: None, footprints: true, subsume: true, max_width: 10_000, max_explore: 1_000_000 }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub events: usize,
    /// Nodes visited while explaining events.
    pub explored: usize,
    pub max_width: usize,
    pub subsumed: usize,
}

#[derive(Clone, Debug)]
pub struct Violation {
    pub index: usize,
    pub now: Time,
    pub event: String,
    pub reason: String,
    /// The profile the event could not be explained from.
    pub profile: Vec<String>,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "event #{} at t={} {} : {}", self.index, self.now, self.event, self.reason)?;
        for n in &self.profile {
            writeln!(f, "  candidate {n}")?;
        }
        Ok(())
    }
}

pub struct Checker<S: Spec> {
    spec: S,
    cfg: Config,
    profile: Vec<Node<S>>,
    states: Interner<S::State>,
    now: Time,
    pub stats: Stats,
}

impl<S: Spec> Checker<S> {
    pub fn new(spec: S, init: S::State, cfg: Config) -> Self {
        Self::starting_at(spec, init, cfg, 0)
    }

    pub fn starting_at(spec: S, init: S::State, cfg: Config, now: Time) -> Self {
        let states = Interner::new();
        let root = Node { state: states.intern(init), pending: BTreeSet::new() };
        Checker { spec, cfg, profile: vec![root], states, now, stats: Stats { max_width: 1, ..Stats::default() } }
    }

    pub fn now(&self) -> Time {
        self.now
    }

    pub fn profile(&self) -> &[Node<S>] {
        &self.profile
    }

    pub fn states(&self) -> impl Iterator<Item = &S::State> {
        self.profile.iter().map(|n| &*n.state)
    }

    /// True if `pred` holds in every candidate state: Accordant's "all terminal" poll check.
    pub fn all(&self, pred: impl Fn(&S::State) -> bool) -> bool {
        self.states().all(pred)
    }

    pub fn invoke(&mut self, call: CallId, op: S::Op) -> Result<(), Violation> {
        self.observe(Event::Invoke(call, op))
    }

    pub fn ret(&mut self, call: CallId, resp: S::Resp) -> Result<(), Violation> {
        self.observe(Event::Return(call, resp))
    }

    pub fn tick(&mut self, to: Time) -> Result<(), Violation> {
        self.observe(Event::Tick(to))
    }

    pub fn quiesce(&mut self) -> Result<(), Violation> {
        self.observe(Event::Quiesce)
    }

    /// A call whose request and response are observed at the same instant.
    pub fn call(&mut self, call: CallId, op: S::Op, resp: S::Resp) -> Result<(), Violation> {
        self.invoke(call, op)?;
        self.ret(call, resp)
    }

    pub fn observe(&mut self, e: Event<S::Op, S::Resp>) -> Result<(), Violation> {
        let index = self.stats.events;
        self.stats.events += 1;
        let Event::Tick(to) = e else {
            return self.instant(index, &e);
        };
        if to < self.now {
            return Err(self.violation(index, &e, format!("time went backwards from {}", self.now)));
        }
        for t in self.instants(to) {
            self.instant(index, &Event::Tick(t))?;
        }
        Ok(())
    }

    /// Every instant in `(now, to]` at which some candidate's work becomes due or
    /// its deadline passes, in order, ending with `to`.
    fn instants(&self, to: Time) -> Vec<Time> {
        let mut ts = BTreeSet::from([to]);
        for n in &self.profile {
            for item in &n.pending {
                match item {
                    Pending::Step { after, by, .. } => ts.extend([Some(*after), *by].into_iter().flatten()),
                    Pending::InFlight { since, must: false, .. } => {
                        ts.extend(self.cfg.request_lifetime.map(|l| since + l));
                    }
                    _ => {}
                }
            }
        }
        ts.into_iter().filter(|t| *t > self.now && *t <= to).collect()
    }

    fn instant(&mut self, index: usize, e: &Event<S::Op, S::Resp>) -> Result<(), Violation> {
        let mut seen = HashSet::new();
        let mut next = Vec::new();
        let mut explored = 0usize;
        for n in &self.profile {
            for p in self.prepare(n, e) {
                self.explain(p, e, &mut seen, &mut next, &mut explored)
                    .map_err(|reason| self.violation(index, e, reason))?;
            }
        }
        self.stats.explored += explored;
        if self.cfg.subsume {
            let before = next.len();
            next = subsume::<S>(next);
            self.stats.subsumed += before - next.len();
        }
        if next.is_empty() {
            return Err(self.violation(index, e, "no candidate state explains this event".into()));
        }
        if next.len() > self.cfg.max_width {
            return Err(self.violation(index, e, format!("profile width {} exceeds max_width", next.len())));
        }
        self.stats.max_width = self.stats.max_width.max(next.len());
        self.profile = next;
        if let Event::Tick(t) = e {
            self.now = *t;
        }
        self.states.collect();
        Ok(())
    }

    fn violation(&self, index: usize, e: &Event<S::Op, S::Resp>, reason: String) -> Violation {
        Violation {
            index,
            now: self.now,
            event: format!("{e:?}"),
            reason,
            profile: self.profile.iter().map(|n| format!("{n:?}")).collect(),
        }
    }

    /// Before time passes a request's lifetime, each branch decides: it took effect
    /// in time (and must linearize before the clock moves on), or it never will.
    fn prepare(&self, n: &Node<S>, e: &Event<S::Op, S::Resp>) -> Vec<Node<S>> {
        let (Event::Tick(t), Some(life)) = (e, self.cfg.request_lifetime) else {
            return vec![n.clone()];
        };
        let expiring: Vec<_> = n
            .pending
            .iter()
            .filter(|i| matches!(i, Pending::InFlight { since, must: false, .. } if since + life < *t))
            .cloned()
            .collect();
        let mut out = Vec::with_capacity(1 << expiring.len());
        for mask in 0u64..(1u64 << expiring.len()) {
            let mut pending = n.pending.clone();
            for (i, item) in expiring.iter().enumerate() {
                pending.remove(item);
                if mask & (1 << i) != 0 {
                    if let Pending::InFlight { call, op, since, .. } = item {
                        pending.insert(Pending::InFlight { call: *call, op: op.clone(), since: *since, must: true });
                    }
                }
            }
            out.push(Node { state: n.state.clone(), pending });
        }
        out
    }

    /// Explores the fewest internal moves that let `e` be consumed from `n`: moves
    /// stop once nothing owed before `e` remains, and only work sharing a footprint
    /// with what is owed is tried. Everything else commutes past `e` and waits.
    fn explain(
        &self,
        n: Node<S>,
        e: &Event<S::Op, S::Resp>,
        seen: &mut HashSet<Node<S>>,
        out: &mut Vec<Node<S>>,
        explored: &mut usize,
    ) -> Result<(), String> {
        let owed = self.owed(&n, e);
        if owed.is_empty() {
            if let Some(m) = self.consume(&n, e)? {
                if seen.insert(m.clone()) {
                    out.push(m);
                }
            }
            return Ok(());
        }
        let relevant = if matches!(e, Event::Quiesce) || !self.cfg.footprints {
            Keys::All
        } else {
            self.relevant(&n, &owed)
        };
        let mut visited: HashSet<Node<S>> = HashSet::new();
        let mut queue = VecDeque::from([n.clone()]);
        visited.insert(n);
        while let Some(m) = queue.pop_front() {
            *explored += 1;
            if *explored > self.cfg.max_explore {
                return Err(format!("explored more than {} nodes", self.cfg.max_explore));
            }
            if self.owed(&m, e).is_empty() {
                if let Some(c) = self.consume(&m, e)? {
                    if seen.insert(c.clone()) {
                        out.push(c);
                    }
                }
                continue;
            }
            for item in &m.pending {
                if !intersects(&relevant, &self.keys(item)) {
                    continue;
                }
                for m2 in self.fire(&m, item) {
                    if !visited.contains(&m2) {
                        visited.insert(m2.clone());
                        queue.push_back(m2);
                    }
                }
            }
        }
        Ok(())
    }

    /// What must happen, at the current time, before `e` can be consumed from `m`.
    fn owed<'a>(&self, m: &'a Node<S>, e: &Event<S::Op, S::Resp>) -> Vec<&'a P<S>> {
        m.pending
            .iter()
            .filter(|item| match item {
                Pending::InFlight { must: true, .. } => true,
                Pending::InFlight { call, .. } => matches!(e, Event::Return(c, _) if c == call),
                Pending::Step { step, must: true, by, .. } => {
                    let overdue = match e {
                        Event::Tick(t) => by.is_some_and(|by| by < *t),
                        Event::Quiesce => true,
                        _ => false,
                    };
                    overdue && self.enabled(item, step, &m.state)
                }
                _ => false,
            })
            .collect()
    }

    fn enabled(&self, item: &P<S>, step: &S::Step, state: &S::State) -> bool {
        matches!(item, Pending::Step { after, .. } if *after <= self.now)
            && !matches!(self.spec.step(step, state, self.now), StepResult::Disabled)
    }

    /// The footprint of what is owed, closed over pending work that shares keys with it.
    fn relevant(&self, n: &Node<S>, owed: &[&P<S>]) -> Keys<S::Key> {
        let mut keys: BTreeSet<S::Key> = BTreeSet::new();
        for item in owed {
            match self.keys(item) {
                Keys::All => return Keys::All,
                Keys::Some(ks) => keys.extend(ks),
            }
        }
        loop {
            let before = keys.len();
            for item in &n.pending {
                let ks = self.keys(item);
                let set = Keys::Some(keys.iter().cloned().collect());
                if intersects(&set, &ks) {
                    match ks {
                        Keys::All => return Keys::All,
                        Keys::Some(ks) => keys.extend(ks),
                    }
                }
            }
            if keys.len() == before {
                return Keys::Some(keys.into_iter().collect());
            }
        }
    }

    fn keys(&self, item: &P<S>) -> Keys<S::Key> {
        match item {
            Pending::InFlight { op, .. } => self.spec.op_keys(op),
            Pending::Step { step, .. } => self.spec.step_keys(step),
            Pending::Responded { .. } => Keys::Some(Vec::new()),
        }
    }

    /// Every node reachable from `m` by firing `item` once, at the current time.
    fn fire(&self, m: &Node<S>, item: &P<S>) -> Vec<Node<S>> {
        let without = || {
            let mut p = m.pending.clone();
            p.remove(item);
            p
        };
        match item {
            Pending::InFlight { call, op, .. } => self
                .spec
                .apply(op, &m.state, self.now)
                .into_iter()
                .map(|o| {
                    let mut p = without();
                    p.insert(Pending::Responded { call: *call, resp: o.resp });
                    self.spawn(&mut p, o.spawn);
                    Node { state: self.states.intern(o.next), pending: p }
                })
                .collect(),
            Pending::Step { step, after, .. } if *after <= self.now => {
                match self.spec.step(step, &m.state, self.now) {
                    StepResult::Disabled => Vec::new(),
                    StepResult::Discharged => vec![Node { state: m.state.clone(), pending: without() }],
                    StepResult::Next(succ) => succ
                        .into_iter()
                        .map(|s| {
                            let mut p = without();
                            self.spawn(&mut p, s.spawn);
                            Node { state: self.states.intern(s.next), pending: p }
                        })
                        .collect(),
                }
            }
            _ => Vec::new(),
        }
    }

    fn spawn(&self, pending: &mut BTreeSet<P<S>>, steps: Vec<Sched<S::Step>>) {
        for Sched { step, at } in steps {
            let after = at.map_or(self.now, |t| t.max(self.now));
            let item = match self.spec.fairness(&step) {
                Fairness::May => Pending::Step { step, after, by: None, must: false },
                Fairness::Eventually { within } => {
                    Pending::Step { step, after, by: within.map(|d| after + d), must: true }
                }
            };
            pending.insert(item);
        }
    }

    /// Applies the observation itself. `Ok(None)` means this node cannot explain it.
    fn consume(&self, m: &Node<S>, e: &Event<S::Op, S::Resp>) -> Result<Option<Node<S>>, String> {
        let mut p = m.pending.clone();
        match e {
            Event::Invoke(call, op) => {
                let reused = p.iter().any(|i| {
                    matches!(i, Pending::InFlight { call: c, .. } | Pending::Responded { call: c, .. } if c == call)
                });
                if reused {
                    return Err(format!("call {call} invoked while still outstanding"));
                }
                p.insert(Pending::InFlight { call: *call, op: op.clone(), since: self.now, must: false });
            }
            Event::Return(call, observed) => {
                let hit = p.iter().find_map(|i| match i {
                    Pending::Responded { call: c, resp } if c == call => {
                        self.spec.admits(resp, observed).then(|| i.clone())
                    }
                    _ => None,
                });
                match hit {
                    Some(i) => {
                        p.remove(&i);
                    }
                    None => return Ok(None),
                }
            }
            Event::Tick(_) | Event::Quiesce => {}
        }
        Ok(Some(Node { state: m.state.clone(), pending: p }))
    }
}

fn intersects<K: Ord>(a: &Keys<K>, b: &Keys<K>) -> bool {
    match (a, b) {
        (Keys::All, Keys::Some(v)) | (Keys::Some(v), Keys::All) => !v.is_empty(),
        (Keys::All, Keys::All) => true,
        (Keys::Some(x), Keys::Some(y)) => x.iter().any(|k| y.contains(k)),
    }
}

/// Work a node may simply never do: dropping it cannot add behaviors.
fn optional<O, R, T>(item: &Pending<O, R, T>) -> bool {
    matches!(item, Pending::Step { must: false, .. })
}

/// Keeps only nodes no other node simulates. Nodes with the same state and the
/// same owed work are compared on optional work: more of it is more behaviors.
fn subsume<S: Spec>(nodes: Vec<Node<S>>) -> Vec<Node<S>> {
    type Group<S> = (Interned<<S as Spec>::State>, Vec<P<S>>);
    let mut groups: HashMap<Group<S>, Vec<usize>> = HashMap::new();
    for (i, n) in nodes.iter().enumerate() {
        let owed: Vec<_> = n.pending.iter().filter(|x| !optional(*x)).cloned().collect();
        groups.entry((n.state.clone(), owed)).or_default().push(i);
    }
    let mut keep = vec![true; nodes.len()];
    for idx in groups.values().filter(|g| g.len() > 1) {
        for &a in idx {
            for &b in idx {
                if a == b || !keep[b] {
                    continue;
                }
                let weaker = nodes[a].pending.iter().filter(|x| optional(*x));
                if weaker.clone().all(|x| nodes[b].pending.contains(x)) {
                    keep[a] = false;
                    break;
                }
            }
        }
    }
    nodes.into_iter().zip(keep).filter_map(|(n, k)| k.then_some(n)).collect()
}
