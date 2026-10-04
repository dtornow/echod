use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::intern::{Interned, Interner};
use crate::{CallId, Fairness, Keys, Spec, StepResult};

/// Work a node still carries. Sorted, so a node's identity is canonical.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Pending<O, R, T> {
    /// Invoked, not yet linearized. Must linearize before its `Return`.
    InFlight { call: CallId, op: O },
    /// Linearized; the spec predicted `resp`, which the `Return` must match.
    Responded { call: CallId, resp: R },
    /// The client gave up. May still take effect by the `ttl`-th later response, or never.
    Ghost { call: CallId, op: O, ttl: u32 },
    /// A ghost this branch decided does take effect, before the current event.
    Forced { call: CallId, op: O },
    /// Background work. `must` with `ttl: Some(k)`: must fire by the `k`-th later response.
    Step { step: T, must: bool, ttl: Option<u32> },
    /// An obligation past its budget: fires before any response while it is enabled.
    Due { step: T },
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event<O, R> {
    Invoke(CallId, O),
    Return(CallId, R),
    /// The client stopped waiting (timeout, reset). The request may still take effect.
    Lost(CallId),
    /// The system is idle: every owed obligation has fired, every lost request has
    /// taken effect or never will.
    Quiesce,
}

#[derive(Clone, Debug)]
pub struct Config {
    /// A lost request may take effect up to the completion of this many later responses.
    pub ghost_ttl: u32,
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
        Config { ghost_ttl: 3, footprints: true, subsume: true, max_width: 10_000, max_explore: 1_000_000 }
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
    pub event: String,
    pub reason: String,
    /// The profile the event could not be explained from.
    pub profile: Vec<String>,
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "event #{} {} : {}", self.index, self.event, self.reason)?;
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
    pub stats: Stats,
}

impl<S: Spec> Checker<S> {
    pub fn new(spec: S, init: S::State, cfg: Config) -> Self {
        let states = Interner::new();
        let root = Node { state: states.intern(init), pending: BTreeSet::new() };
        Checker { spec, cfg, profile: vec![root], states, stats: Stats { max_width: 1, ..Stats::default() } }
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

    pub fn lost(&mut self, call: CallId) -> Result<(), Violation> {
        self.observe(Event::Lost(call))
    }

    pub fn quiesce(&mut self) -> Result<(), Violation> {
        self.observe(Event::Quiesce)
    }

    /// A call whose request and response are observed together.
    pub fn call(&mut self, call: CallId, op: S::Op, resp: S::Resp) -> Result<(), Violation> {
        self.invoke(call, op)?;
        self.ret(call, resp)
    }

    pub fn observe(&mut self, e: Event<S::Op, S::Resp>) -> Result<(), Violation> {
        let index = self.stats.events;
        self.stats.events += 1;
        let mut seen = HashSet::new();
        let mut next = Vec::new();
        let mut explored = 0usize;
        for n in &self.profile {
            for p in self.prepare(n, &e) {
                self.explain(p, &e, &mut seen, &mut next, &mut explored)
                    .map_err(|reason| self.violation(index, &e, reason))?;
            }
        }
        self.stats.explored += explored;
        if self.cfg.subsume {
            let before = next.len();
            next = subsume::<S>(next);
            self.stats.subsumed += before - next.len();
        }
        if next.is_empty() {
            return Err(self.violation(index, &e, "no candidate state explains this event".into()));
        }
        if next.len() > self.cfg.max_width {
            return Err(self.violation(index, &e, format!("profile width {} exceeds max_width", next.len())));
        }
        self.stats.max_width = self.stats.max_width.max(next.len());
        self.profile = next;
        self.states.collect();
        Ok(())
    }

    fn violation(&self, index: usize, e: &Event<S::Op, S::Resp>, reason: String) -> Violation {
        Violation {
            index,
            event: format!("{e:?}"),
            reason,
            profile: self.profile.iter().map(|n| format!("{n:?}")).collect(),
        }
    }

    /// Advances budgets and resolves what expires at this event. Budgets count
    /// responses: an `Invoke` or `Lost` observes nothing, so deferring past one is
    /// free. A ghost that expires branches: it never happened, or it happens now.
    fn prepare(&self, n: &Node<S>, e: &Event<S::Op, S::Resp>) -> Vec<Node<S>> {
        if matches!(e, Event::Invoke(..) | Event::Lost(_)) {
            return vec![n.clone()];
        }
        let quiesce = matches!(e, Event::Quiesce);
        let mut base = BTreeSet::new();
        let mut expiring = Vec::new();
        for item in &n.pending {
            match item {
                Pending::Ghost { call, op, ttl } if *ttl <= 1 || quiesce => expiring.push((*call, op.clone())),
                Pending::Ghost { call, op, ttl } => {
                    base.insert(Pending::Ghost { call: *call, op: op.clone(), ttl: ttl - 1 });
                }
                Pending::Step { step, must: true, ttl } => match ttl {
                    Some(0 | 1) => {
                        base.insert(Pending::Due { step: step.clone() });
                    }
                    None if quiesce => {
                        base.insert(Pending::Due { step: step.clone() });
                    }
                    Some(k) => {
                        base.insert(Pending::Step { step: step.clone(), must: true, ttl: Some(k - 1) });
                    }
                    None => {
                        base.insert(item.clone());
                    }
                },
                _ => {
                    base.insert(item.clone());
                }
            }
        }
        let mut out = Vec::with_capacity(1 << expiring.len());
        for mask in 0u64..(1u64 << expiring.len()) {
            let mut pending = base.clone();
            for (i, (call, op)) in expiring.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    pending.insert(Pending::Forced { call: *call, op: op.clone() });
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

    /// What must happen before `e` can be consumed from `m`.
    fn owed<'a>(&self, m: &'a Node<S>, e: &Event<S::Op, S::Resp>) -> Vec<&'a P<S>> {
        let quiesce = matches!(e, Event::Quiesce);
        m.pending
            .iter()
            .filter(|item| match item {
                Pending::InFlight { call, .. } => matches!(e, Event::Return(c, _) if c == call),
                Pending::Forced { .. } => true,
                Pending::Due { step } => self.enabled(step, &m.state),
                Pending::Step { step, must: true, .. } => quiesce && self.enabled(step, &m.state),
                _ => false,
            })
            .collect()
    }

    fn enabled(&self, step: &S::Step, state: &S::State) -> bool {
        !matches!(self.spec.step(step, state), StepResult::Disabled)
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
            Pending::InFlight { op, .. } | Pending::Ghost { op, .. } | Pending::Forced { op, .. } => {
                self.spec.op_keys(op)
            }
            Pending::Step { step, .. } | Pending::Due { step } => self.spec.step_keys(step),
            Pending::Responded { .. } => Keys::Some(Vec::new()),
        }
    }

    /// Every node reachable from `m` by firing `item` once.
    fn fire(&self, m: &Node<S>, item: &P<S>) -> Vec<Node<S>> {
        let without = || {
            let mut p = m.pending.clone();
            p.remove(item);
            p
        };
        match item {
            Pending::InFlight { op, .. } | Pending::Ghost { op, .. } | Pending::Forced { op, .. } => self
                .spec
                .apply(op, &m.state)
                .into_iter()
                .map(|o| {
                    let mut p = without();
                    if let Pending::InFlight { call, .. } = item {
                        p.insert(Pending::Responded { call: *call, resp: o.resp });
                    }
                    self.spawn(&mut p, o.spawn);
                    Node { state: self.states.intern(o.next), pending: p }
                })
                .collect(),
            Pending::Step { step, .. } | Pending::Due { step } => match self.spec.step(step, &m.state) {
                StepResult::Disabled => Vec::new(),
                StepResult::Discharged => vec![Node { state: m.state.clone(), pending: without() }],
                StepResult::Next(succ) => succ
                    .into_iter()
                    .map(|(s, spawned)| {
                        let mut p = without();
                        self.spawn(&mut p, spawned);
                        Node { state: self.states.intern(s), pending: p }
                    })
                    .collect(),
            },
            Pending::Responded { .. } => Vec::new(),
        }
    }

    fn spawn(&self, pending: &mut BTreeSet<P<S>>, steps: Vec<S::Step>) {
        for step in steps {
            let item = match self.spec.fairness(&step) {
                Fairness::May => Pending::Step { step, must: false, ttl: None },
                Fairness::Eventually { within } => Pending::Step { step, must: true, ttl: within },
            };
            pending.insert(item);
        }
    }

    /// Applies the observation itself. `Ok(None)` means this node cannot explain it.
    fn consume(&self, m: &Node<S>, e: &Event<S::Op, S::Resp>) -> Result<Option<Node<S>>, String> {
        let mut p = m.pending.clone();
        let call_of = |item: &P<S>| match item {
            Pending::InFlight { call, .. }
            | Pending::Responded { call, .. }
            | Pending::Ghost { call, .. }
            | Pending::Forced { call, .. } => Some(*call),
            _ => None,
        };
        match e {
            Event::Invoke(call, op) => {
                if p.iter().any(|i| call_of(i) == Some(*call)) {
                    return Err(format!("call {call} invoked twice"));
                }
                p.insert(Pending::InFlight { call: *call, op: op.clone() });
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
            Event::Lost(call) => {
                let item = p.iter().find(|i| call_of(i) == Some(*call)).cloned();
                match item {
                    Some(Pending::InFlight { call, op }) => {
                        p.remove(&Pending::InFlight { call, op: op.clone() });
                        p.insert(Pending::Ghost { call, op, ttl: self.cfg.ghost_ttl });
                    }
                    Some(i @ Pending::Responded { .. }) => {
                        p.remove(&i);
                    }
                    _ => return Err(format!("call {call} lost but not outstanding")),
                }
            }
            Event::Quiesce => {}
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
    matches!(item, Pending::Ghost { .. } | Pending::Step { must: false, .. })
}

/// Whether optional item `a` (in the weaker node) is covered by `b` (in the stronger).
fn covers<O: Eq, R, T: Eq>(b: &Pending<O, R, T>, a: &Pending<O, R, T>) -> bool {
    match (b, a) {
        (Pending::Ghost { call: c1, op: o1, ttl: t1 }, Pending::Ghost { call: c2, op: o2, ttl: t2 }) => {
            c1 == c2 && o1 == o2 && t1 >= t2
        }
        (Pending::Step { step: s1, .. }, Pending::Step { step: s2, .. }) => s1 == s2,
        _ => false,
    }
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
                if weaker.clone().all(|x| nodes[b].pending.iter().any(|y| covers(y, x))) {
                    keep[a] = false;
                    break;
                }
            }
        }
    }
    nodes.into_iter().zip(keep).filter_map(|(n, k)| k.then_some(n)).collect()
}
