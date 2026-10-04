use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::hashed_set::HashedSet;
use crate::intern::{Interned, Interner};
use crate::{CallId, Engine, Fairness, Footprint, Grouped, Keyed, Touches, Model, Partitioned, Plain, Sched, Time};

type St<S> = <<S as Engine>::M as Model>::State;
type Ex<S> = <<S as Engine>::M as Model>::External;
type Re<S> = <<S as Engine>::M as Model>::Response;
type In<S> = <<S as Engine>::M as Model>::Internal;

/// Work a node still carries. Sorted, so a node's identity is canonical.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Pending<O, R, T> {
    /// Invoked at `since`, not yet linearized. It may take effect at any point
    /// until its `Return`, or never if no `Return` comes. `must`: this branch has
    /// committed to it taking effect before its request lifetime ends.
    /// `early`: answers it could already have gotten by linearizing at an earlier
    /// point where it would not have changed the state. Reads accumulate here
    /// instead of branching the profile.
    InFlight { call: CallId, op: O, since: Time, must: bool, early: BTreeSet<R> },
    /// Linearized; the spec predicted `resp`, which the `Return` must match.
    Responded { call: CallId, resp: R },
    /// Background work, due from `after`. `must`: owed by `by`, or by the next
    /// `Quiesce` if `by` is `None`.
    Step { step: T, after: Time, by: Option<Time>, must: bool },
}

type P<S> = Pending<Ex<S>, Re<S>, In<S>>;

/// One explanation of the history so far.
pub struct Node<S: Engine> {
    pub state: Interned<St<S>>,
    pub pending: HashedSet<P<S>>,
}

impl<S: Engine> Clone for Node<S> {
    fn clone(&self) -> Self {
        Node { state: self.state.clone(), pending: self.pending.clone() }
    }
}

impl<S: Engine> PartialEq for Node<S> {
    fn eq(&self, other: &Self) -> bool {
        self.pending == other.pending && self.state == other.state
    }
}

impl<S: Engine> Eq for Node<S> {}

impl<S: Engine> Hash for Node<S> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.state.hash(h);
        self.pending.hash(h);
    }
}

impl<S: Engine> fmt::Debug for Node<S> {
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
    /// The time the history starts at.
    pub start: Time,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            request_lifetime: None,
            footprints: true,
            subsume: true,
            max_width: 10_000,
            max_explore: 1_000_000,
            start: 0,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub events: usize,
    /// Nodes visited while explaining events.
    pub explored: usize,
    /// The most candidates any one factor held.
    pub max_width: usize,
    /// The most factors held at once.
    pub max_factors: usize,
    /// Factors merged because a request spanned them (a partition touched for
    /// the first time joins without counting as a merge).
    pub merges: usize,
    /// Factors split off again once their partitions were independent.
    pub splits: usize,
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

/// The candidates for one group of partitions. The profile is the product of
/// its factors: any choice in one factor combines with any choice in another.
pub struct Factor<S: Engine> {
    /// The partitions this factor owns; `None` owns everything.
    pub parts: Option<BTreeSet<S::Part>>,
    pub nodes: Vec<Node<S>>,
}

impl<S: Engine> Clone for Factor<S> {
    fn clone(&self) -> Self {
        Factor { parts: self.parts.clone(), nodes: self.nodes.clone() }
    }
}

pub struct Checker<S: Engine> {
    engine: S,
    cfg: Config,
    /// Partitions never touched are still in their initial state, here.
    init: St<S>,
    factors: Vec<Factor<S>>,
    /// The factor an event is being explained in.
    profile: Vec<Node<S>>,
    states: Interner<St<S>>,
    now: Time,
    /// While an event is explained in a factor: the partitions it owns.
    scope: Option<Option<BTreeSet<S::Part>>>,
    /// The first spawned step that left `scope`, if any.
    escaped: std::cell::RefCell<Option<String>>,
    /// A partition of each outstanding call, to find its factor on `Return`.
    calls: HashMap<CallId, S::Part>,
    pub stats: Stats,
}

/// Where an event's footprint lands.
enum Scope<K> {
    All,
    Parts(BTreeSet<K>),
}

impl<M: Model> Checker<Plain<M>> {
    /// Checks `model` as it is: every step may touch everything.
    pub fn new(model: M, init: M::State, cfg: Config) -> Self {
        Checker::with_engine(Plain(model), init, cfg)
    }
}

impl<M: Footprint> Checker<Keyed<M>> {
    /// Checks `model` using its footprints.
    pub fn with_footprints(model: M, init: M::State, cfg: Config) -> Self {
        Checker::with_engine(Keyed(model), init, cfg)
    }
}

impl<M: Partitioned> Checker<Grouped<M>> {
    /// Checks `model` using its footprints and its partitions.
    pub fn with_partitions(model: M, init: M::State, cfg: Config) -> Self {
        Checker::with_engine(Grouped(model), init, cfg)
    }
}

impl<S: Engine> Checker<S> {
    pub fn with_engine(engine: S, init: St<S>, cfg: Config) -> Self {
        let now = cfg.start;
        Checker {
            engine,
            cfg,
            init,
            factors: Vec::new(),
            profile: Vec::new(),
            states: Interner::new(),
            now,
            scope: None,
            escaped: Default::default(),
            calls: HashMap::new(),
            stats: Stats { max_width: 1, ..Stats::default() },
        }
    }

    pub fn now(&self) -> Time {
        self.now
    }

    pub fn factors(&self) -> &[Factor<S>] {
        &self.factors
    }

    /// The candidates, as the product of all factors. Can be large: prefer
    /// [`Checker::width`] and [`Checker::factors`] for sizes.
    pub fn profile(&self) -> Vec<Node<S>> {
        let mut acc: Option<Vec<Node<S>>> = None;
        for f in &self.factors {
            acc = Some(match acc {
                None => f.nodes.clone(),
                Some(a) => self.product(&a, &f.nodes),
            });
        }
        acc.unwrap_or_else(|| vec![Node { state: self.states.intern(self.init.clone()), pending: HashedSet::new() }])
    }

    /// The number of candidates: the product of the factor widths.
    pub fn width(&self) -> u128 {
        self.factors.iter().map(|f| f.nodes.len() as u128).product()
    }

    pub fn states(&self) -> impl Iterator<Item = St<S>> {
        self.profile().into_iter().map(|n| (*n.state).clone())
    }

    /// True if `pred` holds in every candidate state: Accordant's "all terminal" poll check.
    pub fn all(&self, pred: impl Fn(&St<S>) -> bool) -> bool {
        self.states().all(|s| pred(&s))
    }

    pub fn invoke(&mut self, call: CallId, op: Ex<S>) -> Result<(), Violation> {
        self.observe(Event::Invoke(call, op))
    }

    pub fn ret(&mut self, call: CallId, resp: Re<S>) -> Result<(), Violation> {
        self.observe(Event::Return(call, resp))
    }

    pub fn tick(&mut self, to: Time) -> Result<(), Violation> {
        self.observe(Event::Tick(to))
    }

    pub fn quiesce(&mut self) -> Result<(), Violation> {
        self.observe(Event::Quiesce)
    }

    /// A call whose request and response are observed at the same instant.
    /// Atomic: if the response is rejected, the checker is left as it was.
    pub fn call(&mut self, call: CallId, op: Ex<S>, resp: Re<S>) -> Result<(), Violation> {
        let saved = (self.factors.clone(), self.now);
        let r = self.invoke(call, op).and_then(|_| self.ret(call, resp));
        if r.is_err() {
            (self.factors, self.now) = saved;
        }
        r
    }

    /// Every response `op` may get if it is called now and answered now. Does not
    /// change what the checker accepts. This is Accordant's `Allows` used as a
    /// query: the expected responses, without having to write them down.
    pub fn allowed(&mut self, op: &Ex<S>) -> Vec<Re<S>> {
        let saved = (self.factors.clone(), self.stats.clone());
        let scope = self.scope(self.engine.external_keys(op));
        let i = self.gather(scope);
        let out = self.allowed_in(&self.factors[i].nodes, op);
        (self.factors, self.stats) = saved;
        out
    }

    fn allowed_in(&self, nodes: &[Node<S>], op: &Ex<S>) -> Vec<Re<S>> {
        let probe = CallId::MAX;
        let mut out: Vec<Re<S>> = Vec::new();
        let mut explored = 0;
        for n in nodes {
            let mut m = n.clone();
            m.pending.insert(Pending::InFlight { call: probe, op: op.clone(), since: self.now, must: false, early: BTreeSet::new() });
            let owed = self.owed_for(&m, Some((probe, None)), false);
            let relevant = if self.cfg.footprints { self.relevant(&m, &owed) } else { Touches::Everything };
            let _ = self.search(m, &relevant, &mut explored, |x| {
                for i in &x.pending {
                    let found: Vec<&Re<S>> = match i {
                        Pending::Responded { call, resp } if *call == probe => vec![resp],
                        Pending::InFlight { call, early, .. } if *call == probe => early.iter().collect(),
                        _ => continue,
                    };
                    for r in found {
                        if !out.contains(r) {
                            out.push(r.clone());
                        }
                    }
                }
                Ok(x.pending.iter().any(|i| matches!(i, Pending::InFlight { call, .. } if *call == probe)))
            });
        }
        out.sort();
        out
    }

    pub fn observe(&mut self, e: Event<Ex<S>, Re<S>>) -> Result<(), Violation> {
        let index = self.stats.events;
        self.stats.events += 1;
        match &e {
            Event::Invoke(call, op) => {
                let scope = self.scope(self.engine.external_keys(op));
                if let Scope::Parts(ps) = &scope {
                    if let Some(p) = ps.first() {
                        self.calls.insert(*call, p.clone());
                    }
                }
                let i = self.gather(scope);
                self.within(i, |c| c.observe_in(index, &e))
            }
            Event::Return(call, _) => match self.factor_of(*call) {
                Some(i) => {
                    self.within(i, |c| c.observe_in(index, &e))?;
                    self.calls.remove(call);
                    Ok(())
                }
                None => Err(self.violation(index, &e, format!("call {call} is not outstanding"))),
            },
            Event::Tick(to) => {
                if *to < self.now {
                    return Err(self.violation(index, &e, format!("time went backwards from {}", self.now)));
                }
                let (start, saved) = (self.now, self.factors.clone());
                for i in 0..self.factors.len() {
                    self.now = start;
                    if let Err(v) = self.within(i, |c| c.observe_in(index, &e)) {
                        (self.factors, self.now) = (saved, start);
                        return Err(v);
                    }
                }
                self.now = *to;
                Ok(())
            }
            Event::Quiesce => {
                let saved = self.factors.clone();
                for i in 0..self.factors.len() {
                    if let Err(v) = self.within(i, |c| c.observe_in(index, &e)) {
                        self.factors = saved;
                        return Err(v);
                    }
                }
                Ok(())
            }
        }
    }

    /// Runs `f` with factor `i` as the working profile, then checks that no work
    /// escaped the factor's partitions.
    fn within(&mut self, i: usize, f: impl FnOnce(&mut Self) -> Result<(), Violation>) -> Result<(), Violation> {
        self.profile = std::mem::take(&mut self.factors[i].nodes);
        self.scope = Some(self.factors[i].parts.clone());
        let r = f(self);
        self.scope = None;
        self.factors[i].nodes = std::mem::take(&mut self.profile);
        r?;
        self.stats.max_width = self.stats.max_width.max(self.factors[i].nodes.len());
        if let Some(step) = self.escaped.borrow_mut().take() {
            return Err(Violation {
                index: self.stats.events - 1,
                now: self.now,
                event: step,
                reason: "spec error: work reaches outside the partitions of the request or step that spawned it".into(),
                profile: Vec::new(),
            });
        }
        self.split(i);
        Ok(())
    }

    /// Splits factor `i` back into independent factors once nothing links its
    /// partitions: no pending work spans them, and its candidates are exactly the
    /// product of their projections. A merge for one request (a detached create)
    /// then lasts only as long as that request does.
    fn split(&mut self, i: usize) {
        let Some(parts) = &self.factors[i].parts else { return };
        if parts.len() < 2 {
            return;
        }
        let nodes = &self.factors[i].nodes;
        let mut groups: Vec<BTreeSet<S::Part>> = parts.iter().map(|p| BTreeSet::from([p.clone()])).collect();
        for n in nodes {
            for item in &n.pending {
                if matches!(item, Pending::Responded { .. }) {
                    return; // answered by the spec, not yet returned: its footprint is gone
                }
                let Touches::Only(ks) = self.keys(item) else { return };
                let touched: BTreeSet<S::Part> = ks.iter().filter_map(|k| self.engine.part(k)).collect();
                let (linked, rest): (Vec<_>, Vec<_>) = groups.into_iter().partition(|g| !g.is_disjoint(&touched));
                groups = rest;
                groups.push(linked.into_iter().flatten().collect());
            }
        }
        if groups.len() < 2 {
            return;
        }
        let item_part = |item: &P<S>| match self.keys(item) {
            Touches::Only(ks) => ks.first().and_then(|k| self.engine.part(k)),
            Touches::Everything => None,
        };
        let mut factors = Vec::new();
        for g in &groups {
            let mut seen = HashSet::new();
            let mut proj = Vec::new();
            for n in nodes {
                let state = self.states.intern(self.engine.restrict(&n.state, &|p| g.contains(p)));
                let pending = n.pending.iter().filter(|x| item_part(x).is_some_and(|p| g.contains(&p))).cloned().collect();
                let m = Node { state, pending };
                if seen.insert(m.clone()) {
                    proj.push(m);
                }
            }
            factors.push(Factor { parts: Some(g.clone()), nodes: proj });
        }
        let product: u128 = factors.iter().map(|f| f.nodes.len() as u128).product();
        if product != nodes.len() as u128 {
            return; // the candidates correlate across the groups
        }
        self.stats.splits += factors.len() - 1;
        self.factors.splice(i..=i, factors);
        self.stats.max_factors = self.stats.max_factors.max(self.factors.len());
    }

    fn scope(&self, keys: Touches<S::Key>) -> Scope<S::Part> {
        let Touches::Only(ks) = keys else { return Scope::All };
        let mut parts = BTreeSet::new();
        for k in &ks {
            match self.engine.part(k) {
                Some(p) => parts.insert(p),
                None => return Scope::All,
            };
        }
        Scope::Parts(parts)
    }

    /// The index of the one factor that owns `scope`, merging factors and pulling
    /// untouched partitions out of the initial state as needed.
    fn gather(&mut self, scope: Scope<S::Part>) -> usize {
        if let Some(i) = self.factors.iter().position(|f| f.parts.is_none()) {
            return i;
        }
        let (hit, fresh): (Vec<usize>, Factor<S>) = match scope {
            Scope::All => {
                let claimed: BTreeSet<S::Part> =
                    self.factors.iter().flat_map(|f| f.parts.iter().flatten().cloned()).collect();
                let rest = if self.factors.is_empty() {
                    self.init.clone()
                } else {
                    self.engine.restrict(&self.init, &|p| !claimed.contains(p))
                };
                let node = Node { state: self.states.intern(rest), pending: HashedSet::new() };
                ((0..self.factors.len()).collect(), Factor { parts: None, nodes: vec![node] })
            }
            Scope::Parts(parts) => {
                let hit: Vec<usize> = (0..self.factors.len())
                    .filter(|&i| self.factors[i].parts.as_ref().is_some_and(|ps| !ps.is_disjoint(&parts)))
                    .collect();
                let claimed: BTreeSet<S::Part> = hit.iter().flat_map(|&i| self.factors[i].parts.iter().flatten().cloned()).collect();
                let new: BTreeSet<S::Part> = parts.difference(&claimed).cloned().collect();
                let state = self.engine.restrict(&self.init, &|p| new.contains(p));
                let node = Node { state: self.states.intern(state), pending: HashedSet::new() };
                (hit, Factor { parts: Some(new), nodes: vec![node] })
            }
        };
        let mut merged = fresh;
        for &i in hit.iter().rev() {
            let f = self.factors.remove(i);
            merged = Factor {
                parts: match (f.parts, merged.parts) {
                    (Some(a), Some(b)) => Some(a.union(&b).cloned().collect()),
                    _ => None,
                },
                nodes: self.product(&f.nodes, &merged.nodes),
            };
        }
        if hit.len() > 1 {
            self.stats.merges += hit.len() - 1;
        }
        self.factors.push(merged);
        self.stats.max_factors = self.stats.max_factors.max(self.factors.len());
        self.factors.len() - 1
    }

    /// Every combination of a candidate from `a` with one from `b`.
    fn product(&self, a: &[Node<S>], b: &[Node<S>]) -> Vec<Node<S>> {
        let mut out = Vec::with_capacity(a.len() * b.len());
        for x in a {
            for y in b {
                let state = self.engine.join(&x.state, &y.state);
                let pending = x.pending.union(&y.pending);
                out.push(Node { state: self.states.intern(state), pending });
            }
        }
        out
    }

    fn factor_of(&self, call: CallId) -> Option<usize> {
        if let Some(i) = self.factors.iter().position(|f| f.parts.is_none()) {
            return Some(i);
        }
        if let Some(p) = self.calls.get(&call) {
            if let Some(i) = self.factors.iter().position(|f| f.parts.as_ref().is_some_and(|ps| ps.contains(p))) {
                return Some(i);
            }
        }
        self.factors.iter().position(|f| {
            f.nodes.iter().any(|n| {
                n.pending.iter().any(|i| {
                    matches!(i, Pending::InFlight { call: c, .. } | Pending::Responded { call: c, .. } if *c == call)
                })
            })
        })
    }

    /// One event, explained within the working profile.
    fn observe_in(&mut self, index: usize, e: &Event<Ex<S>, Re<S>>) -> Result<(), Violation> {
        let Event::Tick(to) = *e else {
            return self.instant(index, e);
        };
        let saved = (self.profile.clone(), self.now);
        for t in self.instants(to) {
            if let Err(v) = self.instant(index, &Event::Tick(t)) {
                (self.profile, self.now) = saved;
                return Err(v);
            }
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

    fn instant(&mut self, index: usize, e: &Event<Ex<S>, Re<S>>) -> Result<(), Violation> {
        let mut explored = 0usize;
        let mut next = Vec::new();
        let mut seen = HashSet::new();
        for n in &self.profile {
            for p in self.prepare(n, e) {
                let found = match e {
                    Event::Tick(t) => self.before_tick(p, *t, &mut explored),
                    _ => self.explain(p, e, &mut explored),
                }
                .map_err(|reason| self.violation(index, e, reason))?;
                next.extend(found.into_iter().filter(|m| seen.insert(m.clone())));
            }
        }
        if let Event::Tick(t) = *e {
            // The clock moves; whatever is now overdue fires at the new instant, first.
            let old = std::mem::replace(&mut self.now, t);
            let mut after = Vec::new();
            let mut seen = HashSet::new();
            for n in next {
                match self.explain(n, e, &mut explored) {
                    Ok(found) => after.extend(found.into_iter().filter(|m| seen.insert(m.clone()))),
                    Err(reason) => {
                        self.now = old;
                        return Err(self.violation(index, e, reason));
                    }
                }
            }
            next = after;
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
        self.profile = next;
        self.states.collect();
        Ok(())
    }

    fn violation(&self, index: usize, e: &Event<Ex<S>, Re<S>>, reason: String) -> Violation {
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
    fn prepare(&self, n: &Node<S>, e: &Event<Ex<S>, Re<S>>) -> Vec<Node<S>> {
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
                    if let Pending::InFlight { call, op, since, early, .. } = item {
                        let early = early.clone();
                        pending.insert(Pending::InFlight { call: *call, op: op.clone(), since: *since, must: true, early });
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
    fn explain(&self, n: Node<S>, e: &Event<Ex<S>, Re<S>>, explored: &mut usize) -> Result<Vec<Node<S>>, String> {
        let owed = self.owed(&n, e);
        if owed.is_empty() {
            return Ok(self.consume(&n, e)?.into_iter().collect());
        }
        let relevant = if matches!(e, Event::Quiesce) || !self.cfg.footprints {
            Touches::Everything
        } else {
            self.relevant(&n, &owed)
        };
        let mut out = Vec::new();
        self.search(n, &relevant, explored, |m| {
            if !self.owed(m, e).is_empty() {
                return Ok(true);
            }
            out.extend(self.consume(m, e)?);
            Ok(false)
        })?;
        Ok(out)
    }

    /// Before the clock moves to `t`, anything that may happen at the current
    /// instant and could change what happens at `t` gets its chance: in-flight
    /// calls may linearize and lazy work may fire, on the keys of the work that
    /// falls due by `t`. Every point along the way is a candidate. A call whose
    /// request lifetime ends here and that this branch says took effect must have.
    fn before_tick(&self, n: Node<S>, t: Time, explored: &mut usize) -> Result<Vec<Node<S>>, String> {
        let forced: Vec<&P<S>> = n
            .pending
            .iter()
            .filter(|i| match i {
                Pending::InFlight { must, .. } => *must,
                Pending::Step { must: true, by: Some(by), .. } => *by <= t,
                _ => false,
            })
            .collect();
        if forced.is_empty() {
            return Ok(vec![n]);
        }
        let relevant = if self.cfg.footprints { self.relevant(&n, &forced) } else { Touches::Everything };
        let mut out = Vec::new();
        self.search(n, &relevant, explored, |m| {
            let ready = !m.pending.iter().any(|i| matches!(i, Pending::InFlight { must: true, .. }))
                && !self.has_overdue(m);
            if ready {
                out.push(m.clone());
            }
            Ok(true)
        })?;
        Ok(out)
    }

    /// Breadth-first over moves on `relevant` keys. `visit` returns whether to keep
    /// expanding a node. Overdue work has priority: while a node has some, nothing
    /// else may fire, so an overdue timer is never overtaken.
    fn search(
        &self,
        n: Node<S>,
        relevant: &Touches<S::Key>,
        explored: &mut usize,
        mut visit: impl FnMut(&Node<S>) -> Result<bool, String>,
    ) -> Result<(), String> {
        let mut visited: HashSet<Node<S>> = HashSet::from([n.clone()]);
        let mut queue = VecDeque::from([n]);
        while let Some(m) = queue.pop_front() {
            *explored += 1;
            if *explored > self.cfg.max_explore {
                return Err(format!("explored more than {} nodes", self.cfg.max_explore));
            }
            if !visit(&m)? {
                continue;
            }
            let urgent = self.has_overdue(&m);
            for item in &m.pending {
                if !self.can_fire(item) {
                    continue;
                }
                if urgent && !self.is_overdue(item, &m.state) {
                    continue;
                }
                if !urgent && !intersects(relevant, &self.keys(item)) {
                    continue;
                }
                for m2 in self.fire(&m, item) {
                    if visited.insert(m2.clone()) {
                        queue.push_back(m2);
                    }
                }
            }
        }
        Ok(())
    }

    /// An obligation whose deadline is now or past and that can fire: it must fire
    /// before anything else is observed or happens at this instant.
    fn is_overdue(&self, item: &P<S>, state: &St<S>) -> bool {
        match item {
            Pending::Step { step, must: true, by: Some(by), .. } => *by <= self.now && self.enabled(item, step, state),
            _ => false,
        }
    }

    fn has_overdue(&self, m: &Node<S>) -> bool {
        m.pending.iter().any(|i| self.is_overdue(i, &m.state))
    }

    /// What must happen, at the current time, before `e` can be consumed from `m`.
    fn owed<'a>(&self, m: &'a Node<S>, e: &Event<Ex<S>, Re<S>>) -> Vec<&'a P<S>> {
        let returning = match e {
            Event::Return(c, r) => Some((*c, Some(r))),
            _ => None,
        };
        self.owed_for(m, returning, matches!(e, Event::Quiesce))
    }

    /// `returning`: the call being answered, and the answer if known. A call whose
    /// early answers already admit it owes nothing.
    fn owed_for<'a>(
        &self,
        m: &'a Node<S>,
        returning: Option<(CallId, Option<&Re<S>>)>,
        quiesce: bool,
    ) -> Vec<&'a P<S>> {
        m.pending
            .iter()
            .filter(|item| match item {
                Pending::InFlight { must: true, .. } => true,
                Pending::InFlight { call, early, .. } => match returning {
                    Some((c, obs)) if c == *call => !obs.is_some_and(|o| early.iter().any(|r| self.engine.model().admits(r, o))),
                    _ => false,
                },
                Pending::Step { step, must: true, .. } => {
                    self.is_overdue(item, &m.state) || (quiesce && self.enabled(item, step, &m.state))
                }
                _ => false,
            })
            .collect()
    }

    fn enabled(&self, item: &P<S>, step: &In<S>, state: &St<S>) -> bool {
        matches!(item, Pending::Step { after, .. } if *after <= self.now)
            && !self.engine.model().internal(step, state, self.now).is_empty()
    }

    /// The footprint of what is owed, closed over pending work that shares keys with it.
    fn relevant(&self, n: &Node<S>, owed: &[&P<S>]) -> Touches<S::Key> {
        let mut keys: BTreeSet<S::Key> = BTreeSet::new();
        for item in owed {
            match self.keys(item) {
                Touches::Everything => return Touches::Everything,
                Touches::Only(ks) => keys.extend(ks),
            }
        }
        loop {
            let before = keys.len();
            for item in n.pending.iter().filter(|i| self.can_fire(i)) {
                match self.keys(item) {
                    Touches::Everything => return Touches::Everything,
                    Touches::Only(ks) => {
                        if ks.iter().any(|k| keys.contains(k)) {
                            keys.extend(ks);
                        }
                    }
                }
            }
            if keys.len() == before {
                return Touches::Only(keys.into_iter().collect());
            }
        }
    }

    /// Whether `item` could fire at the current time at all: a call in flight, or
    /// a step whose time has come. Cheap, so it filters before footprints are built.
    fn can_fire(&self, item: &P<S>) -> bool {
        match item {
            Pending::InFlight { .. } => true,
            Pending::Step { after, .. } => *after <= self.now,
            Pending::Responded { .. } => false,
        }
    }

    fn keys(&self, item: &P<S>) -> Touches<S::Key> {
        match item {
            Pending::InFlight { op, .. } => self.engine.external_keys(op),
            Pending::Step { step, .. } => self.engine.internal_keys(step),
            Pending::Responded { .. } => Touches::Only(Vec::new()),
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
            Pending::InFlight { call, op, since, must, early } => {
                let outs = self.engine.model().external(op, &m.state, self.now);
                let read_only = outs.iter().all(|o| o.spawn.is_empty() && o.next == *m.state);
                if !read_only {
                    return outs
                        .into_iter()
                        .map(|o| {
                            let mut p = without();
                            p.insert(Pending::Responded { call: *call, resp: o.resp });
                            self.spawn(&mut p, o.spawn);
                            Node { state: self.states.intern(o.next), pending: p }
                        })
                        .collect();
                }
                // Linearizing here changes nothing but the answer: remember the
                // answer instead of placing the call.
                let mut seen = early.clone();
                seen.extend(outs.into_iter().map(|o| o.resp));
                if *must {
                    return seen
                        .into_iter()
                        .map(|resp| {
                            let mut p = without();
                            p.insert(Pending::Responded { call: *call, resp });
                            Node { state: m.state.clone(), pending: p }
                        })
                        .collect();
                }
                let mut p = without();
                p.insert(Pending::InFlight { call: *call, op: op.clone(), since: *since, must: false, early: seen });
                vec![Node { state: m.state.clone(), pending: p }]
            }
            Pending::Step { step, after, .. } if *after <= self.now => {
                self.engine
                    .model()
                    .internal(step, &m.state, self.now)
                    .into_iter()
                    .map(|s| {
                        let mut p = without();
                        self.spawn(&mut p, s.spawn);
                        Node { state: self.states.intern(s.next), pending: p }
                    })
                    .collect()
            }
            _ => Vec::new(),
        }
    }

    fn spawn(&self, pending: &mut HashedSet<P<S>>, steps: Vec<Sched<In<S>>>) {
        for Sched { step, at } in steps {
            if let Some(Some(parts)) = &self.scope {
                let escaped = match self.engine.internal_keys(&step) {
                    Touches::Everything => true,
                    Touches::Only(ks) => ks.iter().any(|k| self.engine.part(k).is_none_or(|p| !parts.contains(&p))),
                };
                if escaped {
                    self.escaped.borrow_mut().get_or_insert_with(|| format!("{step:?}"));
                }
            }
            let after = at.map_or(self.now, |t| t.max(self.now));
            let item = match self.engine.model().fairness(&step) {
                Fairness::May => Pending::Step { step, after, by: None, must: false },
                Fairness::Eventually { within } => {
                    Pending::Step { step, after, by: within.map(|d| after + d), must: true }
                }
            };
            pending.insert(item);
        }
    }

    /// Applies the observation itself. `Ok(None)` means this node cannot explain it.
    fn consume(&self, m: &Node<S>, e: &Event<Ex<S>, Re<S>>) -> Result<Option<Node<S>>, String> {
        let mut p = m.pending.clone();
        match e {
            Event::Invoke(call, op) => {
                let reused = p.iter().any(|i| {
                    matches!(i, Pending::InFlight { call: c, .. } | Pending::Responded { call: c, .. } if c == call)
                });
                if reused {
                    return Err(format!("call {call} invoked while still outstanding"));
                }
                p.insert(Pending::InFlight { call: *call, op: op.clone(), since: self.now, must: false, early: BTreeSet::new() });
            }
            Event::Return(call, observed) => {
                let hit = p.iter().find_map(|i| match i {
                    Pending::Responded { call: c, resp } if c == call => {
                        self.engine.model().admits(resp, observed).then(|| i.clone())
                    }
                    Pending::InFlight { call: c, early, .. } if c == call => {
                        early.iter().any(|r| self.engine.model().admits(r, observed)).then(|| i.clone())
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

fn intersects<K: Ord>(a: &Touches<K>, b: &Touches<K>) -> bool {
    match (a, b) {
        (Touches::Everything, Touches::Only(v)) | (Touches::Only(v), Touches::Everything) => !v.is_empty(),
        (Touches::Everything, Touches::Everything) => true,
        (Touches::Only(x), Touches::Only(y)) => x.iter().any(|k| y.contains(k)),
    }
}

/// Work a node may simply never do: dropping it cannot add behaviors.
fn optional<O, R, T>(item: &Pending<O, R, T>) -> bool {
    matches!(item, Pending::Step { must: false, .. })
}

/// An item with its early answers cleared, so calls compare by identity alone.
fn skeleton<O: Clone, R: Clone, T: Clone>(item: &Pending<O, R, T>) -> Pending<O, R, T> {
    match item {
        Pending::InFlight { call, op, since, must, .. } => {
            Pending::InFlight { call: *call, op: op.clone(), since: *since, must: *must, early: BTreeSet::new() }
        }
        _ => item.clone(),
    }
}

/// Whether node `b` can do everything node `a` can: same state and same owed
/// work, at least `a`'s optional work, and at least `a`'s early answers per call.
fn simulates<S: Engine>(b: &Node<S>, a: &Node<S>) -> bool {
    a.pending.iter().all(|x| match x {
        Pending::InFlight { call, early, .. } => b.pending.iter().any(|y| {
            matches!(y, Pending::InFlight { call: c, early: e, .. } if c == call && early.is_subset(e))
        }),
        _ if optional(x) => b.pending.contains(x),
        _ => true,
    })
}

/// Keeps only nodes no other node simulates.
fn subsume<S: Engine>(nodes: Vec<Node<S>>) -> Vec<Node<S>> {
    type Group<S> = (Interned<St<S>>, Vec<P<S>>);
    let mut groups: HashMap<Group<S>, Vec<usize>> = HashMap::new();
    for (i, n) in nodes.iter().enumerate() {
        let owed: Vec<_> = n.pending.iter().filter(|x| !optional(*x)).map(skeleton).collect();
        groups.entry((n.state.clone(), owed)).or_default().push(i);
    }
    let mut keep = vec![true; nodes.len()];
    for idx in groups.values().filter(|g| g.len() > 1) {
        for &a in idx {
            for &b in idx {
                if a != b && keep[b] && simulates(&nodes[b], &nodes[a]) {
                    keep[a] = false;
                    break;
                }
            }
        }
    }
    nodes.into_iter().zip(keep).filter_map(|(n, k)| k.then_some(n)).collect()
}
