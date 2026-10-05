use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::certificate::{self, Certificate, Silent, Work};
use crate::hashed_set::HashedSet;
use crate::intern::{Interned, Interner};
use crate::{CallId, Data, Engine, Footprint, Grouped, Keyed, Touches, Model, Partitioned, Plain, Sched, Time};

type St<S> = <<S as Engine>::M as Model>::State;
type Ex<S> = <<S as Engine>::M as Model>::External;
type Re<S> = <<S as Engine>::M as Model>::Response;
type In<S> = <<S as Engine>::M as Model>::Internal;
type Ms<S> = <<S as Engine>::M as Model>::Dispatch;

/// Work a node still carries. Sorted, so a node's identity is canonical.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Pending<O, R, T, G> {
    /// Invoked, not yet linearized. It may take effect at any point until its
    /// `Return`, or never if no `Return` comes. `early`: answers it could
    /// already have gotten by linearizing at an earlier point where it would
    /// not have changed the state. Reads accumulate here instead of branching
    /// the profile.
    InFlight { call: CallId, op: O, early: BTreeSet<R> },
    /// Linearized; the spec predicted `resp`, which the `Return` must match.
    Responded { call: CallId, resp: R },
    /// A message the server sent and the client has not received yet, `count`
    /// times over. It may be received later, or never.
    Sent { msg: G, count: u32 },
    /// Background work, due from `after` on the model's clock, `count` times
    /// over: started twice, it runs twice. `must`: owed by `by`; with no `by`,
    /// it runs when an observation needs it, or never.
    Step { step: T, after: Time, by: Option<Time>, must: bool, count: u32 },
}

type P<S> = Pending<Ex<S>, Re<S>, In<S>, Ms<S>>;

/// What a candidate did, recorded while certificates are on. The checker's
/// own view of a move: by value, before positions and early answers are
/// resolved into [`Move`]s.
#[derive(Clone, Debug)]
enum Record<O, R, T, G> {
    Obs(Event<O, R, G>),
    Effect { call: CallId, j: usize },
    /// A read-only call could take effect here with outcome `j`, answering `res`.
    Early { call: CallId, j: usize, res: R },
    Run { work: Work<T>, j: usize },
}

struct Link<O, R, T, G> {
    rec: Record<O, R, T, G>,
    prev: Trail<O, R, T, G>,
}

/// A candidate's history, newest first, sharing its prefix with its parent's.
pub struct Trail<O, R, T, G>(Option<std::rc::Rc<Link<O, R, T, G>>>);

impl<O, R, T, G> Clone for Trail<O, R, T, G> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

/// Unlinks iteratively: a long history would overflow the stack dropping
/// recursively.
impl<O, R, T, G> Drop for Trail<O, R, T, G> {
    fn drop(&mut self) {
        let mut at = self.0.take();
        while let Some(rc) = at {
            match std::rc::Rc::try_unwrap(rc) {
                Ok(mut link) => at = link.prev.0.take(),
                Err(_) => break,
            }
        }
    }
}

impl<O, R, T, G> Default for Trail<O, R, T, G> {
    fn default() -> Self {
        Self(None)
    }
}

impl<O: Clone, R: Clone, T: Clone, G: Clone> Trail<O, R, T, G> {
    fn push(&self, rec: Record<O, R, T, G>) -> Self {
        Self(Some(std::rc::Rc::new(Link { rec, prev: self.clone() })))
    }

    /// Oldest first.
    fn records(&self) -> Vec<Record<O, R, T, G>> {
        let mut out = Vec::new();
        let mut at = &self.0;
        while let Some(link) = at {
            out.push(link.rec.clone());
            at = &link.prev.0;
        }
        out.reverse();
        out
    }
}

type Tr<S> = Trail<Ex<S>, Re<S>, In<S>, Ms<S>>;
type Rec<S> = Record<Ex<S>, Re<S>, In<S>, Ms<S>>;

/// One explanation of the history so far.
pub struct Node<S: Engine> {
    pub state: Interned<St<S>>,
    pub pending: HashedSet<P<S>>,
    /// How this candidate got here. Not part of its identity.
    trail: Tr<S>,
}

impl<S: Engine> Clone for Node<S> {
    fn clone(&self) -> Self {
        Node { state: self.state.clone(), pending: self.pending.clone(), trail: self.trail.clone() }
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

/// What a client observes. No time: the order of a trace is the order one
/// observer saw, and time is the model's own ([`Model::now`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event<X, R, D> {
    /// The client sent a request.
    Invoke { call: CallId, req: X },
    /// The client got the response to that call.
    Return { call: CallId, res: R },
    /// The client got a dispatch the server sent on its own.
    Receive { msg: D },
}

/// What the checker steps on internally: the observations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Ev<O, R, G> {
    Invoke(CallId, O),
    Return(CallId, R),
    /// The client received a message the server sent on its own.
    Receive(G),
}

#[derive(Clone, Debug)]
pub struct Config {
    /// Prune work whose footprint is disjoint from what an observation needs.
    pub footprints: bool,
    /// Drop nodes another node can simulate (it carries a superset of optional work).
    pub subsume: bool,
    /// Fail rather than let the profile grow past this.
    pub max_width: usize,
    /// Fail rather than explore more nodes than this for one event.
    pub max_explore: usize,
    /// Record each candidate's moves, so [`Checker::certified`] can back the
    /// verdict with a certificate. Costs memory proportional to the history.
    pub certify: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            footprints: true,
            subsume: true,
            max_width: 10_000,
            max_explore: 1_000_000,
            certify: false,
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

/// Why a trace was not accepted. Either the checker showed no execution of the
/// model produces it ([`Verdict::Ko`]), or it gave up before deciding
/// ([`Verdict::Unknown`]): a budget ran out, the checker was misused, or a
/// certificate failed to replay (a checker bug, never a verdict on the trace).
#[derive(Clone, Debug)]
pub struct Violation {
    pub index: usize,
    pub event: String,
    pub reason: String,
    /// The profile the event could not be explained from.
    pub profile: Vec<String>,
    /// The checker gave up: the trace may or may not be valid.
    pub unknown: bool,
}

/// Reasons that are not verdicts start with this.
const GAVE_UP: &str = "gave up: ";

fn gave_up(reason: &str) -> bool {
    reason.starts_with(GAVE_UP)
}

/// The checker's answer about a trace.
#[derive(Debug)]
pub enum Verdict<T> {
    /// Some execution of the model produces the trace (with a certificate,
    /// when one was asked for).
    Ok(T),
    /// No execution of the model produces the trace.
    Ko(Violation),
    /// The checker gave up before deciding.
    Unknown(Violation),
}

impl<T> From<Result<T, Violation>> for Verdict<T> {
    fn from(r: Result<T, Violation>) -> Self {
        match r {
            Ok(t) => Verdict::Ok(t),
            Err(v) if v.unknown => Verdict::Unknown(v),
            Err(v) => Verdict::Ko(v),
        }
    }
}

impl<T> Verdict<T> {
    pub fn is_ok(&self) -> bool {
        matches!(self, Verdict::Ok(_))
    }

    pub fn is_ko(&self) -> bool {
        matches!(self, Verdict::Ko(_))
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Verdict::Unknown(_))
    }
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = if self.unknown { "unknown" } else { "violation" };
        writeln!(f, "{what} at event #{} {} : {}", self.index, self.event, self.reason)?;
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
    /// The initial state, for certificates.
    init: St<S>,
    /// The state of partitions no factor holds: initial, except for what steps
    /// that touched everything did to it (moved the clock).
    rest: St<S>,
    /// Every partition a factor has held.
    known: BTreeSet<S::Part>,
    /// Calls the history says never return: they may take effect at any point,
    /// or never.
    orphans: HashSet<CallId>,
    /// In a complete history, the response each call gets, so a depth-first
    /// search takes only effects that answer it (Porcupine's pruning). Empty
    /// when call ids repeat.
    answers: HashMap<CallId, Re<S>>,
    /// A clock move in flight, explained in every factor on its own.
    broadcasting: Option<(CallId, Ex<S>, usize)>,
    factors: Vec<Factor<S>>,
    /// The factor an event is being explained in.
    profile: Vec<Node<S>>,
    states: Interner<St<S>>,
    /// While an event is explained in a factor: the partitions it owns.
    scope: Option<Option<BTreeSet<S::Part>>>,
    /// The first spawned step that left `scope`, if any.
    escaped: std::cell::RefCell<Option<String>>,
    /// A partition of each outstanding call, to find its factor on `Return`.
    calls: HashMap<CallId, S::Part>,
    /// Call ids `check_calls` hands out; far from the ids callers pick themselves.
    next_call: CallId,
    /// Record each candidate's moves, for a certificate.
    recording: bool,
    /// While recording: the observations so far, which the certificate must show.
    observed: Vec<Event<Ex<S>, Re<S>, Ms<S>>>,
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
        let recording = cfg.certify;
        Checker {
            engine,
            cfg,
            rest: init.clone(),
            known: BTreeSet::new(),
            broadcasting: None,
            orphans: HashSet::new(),
            answers: HashMap::new(),
            init,
            factors: Vec::new(),
            profile: Vec::new(),
            states: Interner::new(),
            scope: None,
            escaped: Default::default(),
            calls: HashMap::new(),
            next_call: 1 << 62,
            recording,
            observed: Vec::new(),
            stats: Stats { max_width: 1, ..Stats::default() },
        }
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
        acc.unwrap_or_else(|| vec![Node { state: self.states.intern(self.rest.clone()), pending: HashedSet::new(), trail: Default::default() }])
    }

    /// The number of candidates: the product of the factor widths.
    pub fn width(&self) -> u128 {
        self.factors.iter().map(|f| f.nodes.len() as u128).product()
    }

    pub fn states(&self) -> impl Iterator<Item = St<S>> {
        self.profile().into_iter().map(|n| (*n.state).clone())
    }

    /// Requests worth trying next, with why: the model's suggestions for every
    /// state the system may be in (at most `limit` states), each once. For a
    /// fuzz driver: the checker knows what the server may have done; the model
    /// knows what is interesting to ask then.
    pub fn suggestions(&self, limit: usize) -> Vec<(Ex<S>, &'static str)>
    where
        S::M: crate::Explore,
        Ex<S>: PartialEq,
    {
        use crate::Explore;
        let mut out: Vec<(Ex<S>, &'static str)> = Vec::new();
        for s in self.states().take(limit) {
            for x in self.engine.model().suggest(&s) {
                if !out.contains(&x) {
                    out.push(x);
                }
            }
        }
        out
    }

    /// True if `pred` holds in every candidate state: Accordant's "all terminal" poll check.
    pub fn all(&self, pred: impl Fn(&St<S>) -> bool) -> bool {
        self.states().all(|s| pred(&s))
    }

    /// One observation.
    pub fn observe(&mut self, e: Event<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        self.apply(match e {
            Event::Invoke { call, req } => Ev::Invoke(call, req),
            Event::Return { call, res } => Ev::Return(call, res),
            Event::Receive { msg } => Ev::Receive(msg),
        })
    }

    /// A request sent now.
    pub fn invoke(&mut self, call: CallId, req: Ex<S>) -> Result<(), Violation> {
        self.apply(Ev::Invoke(call, req))
    }

    /// A response received now.
    pub fn ret(&mut self, call: CallId, res: Re<S>) -> Result<(), Violation> {
        self.apply(Ev::Return(call, res))
    }

    /// A dispatch received now.
    pub fn receive(&mut self, msg: Ms<S>) -> Result<(), Violation> {
        self.apply(Ev::Receive(msg))
    }

    /// A call whose request and response are observed now.
    /// Atomic: if the response is rejected, the checker is left as it was.
    pub fn call(&mut self, call: CallId, req: Ex<S>, res: Re<S>) -> Result<(), Violation> {
        let saved = (self.factors.clone(), self.rest.clone(), self.broadcasting.clone(), self.observed.len());
        let r = self.invoke(call, req).and_then(|_| self.ret(call, res));
        if r.is_err() {
            (self.factors, self.rest, self.broadcasting) = (saved.0, saved.1, saved.2);
            self.observed.truncate(saved.3);
        }
        r
    }

    /// Checks a whole trace: feeds its observations in order and stops at the
    /// first one no run of the model can explain. The trace can be a `Vec`, or
    /// any iterator, including one that generates observations lazily.
    ///
    /// The error's `index` is the position of that observation in `trace`.
    pub fn check<I>(&mut self, trace: I) -> Result<&Stats, Violation>
    where
        I: IntoIterator<Item = Event<Ex<S>, Re<S>, Ms<S>>>,
    {
        for (i, e) in trace.into_iter().enumerate() {
            self.observe(e).map_err(|v| Violation { index: i, ..v })?;
        }
        Ok(&self.stats)
    }

    /// Checks a complete history, as [`Checker::check`] does, using what only the
    /// whole history tells: which calls never return. Such a call may take
    /// effect at any point or never, so a candidate that still has it in flight
    /// can do everything one that applied it can, given the same state, and the
    /// checker keeps only the first. A Jepsen history with many `:info`
    /// operations needs this.
    pub fn check_history(&mut self, trace: &[Event<Ex<S>, Re<S>, Ms<S>>]) -> Result<&Stats, Violation> {
        self.mark_orphans(trace);
        self.check(trace.iter().cloned())
    }

    /// Calls the history invokes and never answers.
    fn mark_orphans(&mut self, trace: &[Event<Ex<S>, Re<S>, Ms<S>>]) {
        let mut open = HashSet::new();
        for e in trace {
            match e {
                Event::Invoke { call, .. } => {
                    open.insert(*call);
                }
                Event::Return { call, .. } => {
                    open.remove(call);
                }
                Event::Receive { .. } => {}
            }
        }
        self.orphans.extend(open);
    }

    /// Checks a complete history depth first, like Porcupine: instead of
    /// keeping every explanation alive, it commits to one way of explaining
    /// each event and backtracks when a later event can't be explained,
    /// remembering which (position, candidate) pairs already failed. On a
    /// valid history it rarely pays for the alternatives; an invalid one it
    /// still has to search exhaustively.
    ///
    /// Each event is explained as [`Checker::check`] explains it, so the
    /// verdict is the same. On success, the path found is the history's
    /// explanation: [`Checker::certified`] turns it into a certificate.
    /// With partitions (and without certificates), a history whose events each
    /// stay in one partition is split by partition first, and each part is
    /// checked on its own.
    ///
    /// Needs a fresh checker, and leaves it fit only for [`Checker::certified`].
    pub fn check_complete(&mut self, trace: &[Event<Ex<S>, Re<S>, Ms<S>>]) -> Result<&Stats, Violation> {
        if self.stats.events > 0 {
            return Err(Violation { index: 0, event: "check_complete".into(), reason: "gave up: needs a fresh checker".into(), profile: Vec::new(), unknown: true });
        }
        self.mark_orphans(trace);
        self.answers = answers(trace);
        if !self.recording && self.engine.partitioned() {
            if let Some(parts) = self.split_by_part(trace) {
                // Round robin, each partition's search resumed with a doubling
                // budget: one hard partition must not hold up a refutation
                // another finds quickly (Porcupine checks partitions in
                // parallel for the same reason).
                let mut open = Vec::new();
                for (part, sub) in parts {
                    let init = self.engine.restrict(&self.rest, &|p| *p == part);
                    let events: Vec<_> = sub.iter().map(|(_, e)| e.clone()).collect();
                    let run = self.dfs_start(init, &events).map_err(|v| Violation { index: sub[v.index].0, ..v })?;
                    open.push((part, sub, run));
                }
                let mut budget = 1_000;
                let mut spent = 0usize;
                while !open.is_empty() {
                    let mut still = Vec::new();
                    for (part, sub, mut run) in open {
                        self.scope = Some(Some(BTreeSet::from([part.clone()])));
                        let r = self.dfs_resume(&mut run, budget);
                        self.scope = None;
                        if let Some(step) = self.escaped.borrow_mut().take() {
                            let reason = "gave up: spec error: work reaches outside the partitions of the request or step that spawned it";
                            return Err(Violation { index: 0, event: step, reason: reason.into(), profile: Vec::new(), unknown: true });
                        }
                        match r {
                            Some(Ok(_)) => {}
                            Some(Err(v)) => return Err(Violation { index: sub[v.index].0, ..v }),
                            None => still.push((part, sub, run)),
                        }
                    }
                    spent += budget * still.len();
                    if spent > self.cfg.max_explore {
                        let (_, sub, run) = &still[0];
                        let j = run.stack.last().map_or(0, |f| f.i);
                        let reason = format!("{GAVE_UP}explored more than {} nodes", self.cfg.max_explore);
                        return Err(Violation { index: sub[j].0, event: format!("{:?}", run.evs[j]), reason, profile: Vec::new(), unknown: true });
                    }
                    open = still;
                    budget = budget.saturating_mul(2);
                }
                self.stats.events += trace.len();
                return Ok(&self.stats);
            }
        }
        let node = self.dfs(self.init.clone(), trace)?;
        self.factors = vec![Factor { parts: None, nodes: vec![node] }];
        if self.recording {
            self.observed = trace.to_vec();
        }
        self.stats.events += trace.len();
        Ok(&self.stats)
    }

    /// The history's events grouped by the one partition each stays in, with
    /// their positions; `None` if some event spans partitions or moves the clock.
    #[allow(clippy::type_complexity)]
    fn split_by_part(&self, trace: &[Event<Ex<S>, Re<S>, Ms<S>>]) -> Option<Vec<(S::Part, Vec<(usize, Event<Ex<S>, Re<S>, Ms<S>>)>)>> {
        let one = |keys| match self.scope(keys) {
            Scope::Parts(ps) if ps.len() == 1 => ps.into_iter().next(),
            _ => None,
        };
        let mut of_call = HashMap::new();
        let mut groups: std::collections::BTreeMap<S::Part, Vec<_>> = Default::default();
        for (i, e) in trace.iter().enumerate() {
            let part = match e {
                Event::Invoke { call, req } => {
                    if self.engine.moves_clock(req) {
                        return None;
                    }
                    let p = one(self.engine.external_keys(req))?;
                    of_call.insert(*call, p.clone());
                    p
                }
                Event::Return { call, .. } => of_call.get(call)?.clone(),
                Event::Receive { msg } => one(self.engine.dispatch_keys(msg))?,
            };
            groups.entry(part).or_default().push((i, e.clone()));
        }
        Some(groups.into_iter().collect())
    }

    /// Depth first through `trace` from `init`, one move at a time: a
    /// candidate after the last event, or the violation at the deepest event
    /// reached.
    ///
    /// From a candidate before event `i`: if nothing is owed before the event,
    /// the event is consumed (it commutes with any move made after it, so
    /// nothing is lost by consuming it first). Otherwise each single move on
    /// the keys of what is owed is a branch, calls in the order they were
    /// invoked. A (position, candidate) pair is explored once.
    fn dfs(&mut self, init: St<S>, trace: &[Event<Ex<S>, Re<S>, Ms<S>>]) -> Result<Node<S>, Violation> {
        let mut run = self.dfs_start(init, trace)?;
        let budget = self.cfg.max_explore;
        self.dfs_resume(&mut run, budget).unwrap_or_else(|| {
            let j = run.stack.last().map_or(0, |f| f.i);
            let reason = format!("{GAVE_UP}explored more than {budget} nodes");
            Err(Violation { index: j, event: format!("{:?}", run.evs[j]), reason, profile: Vec::new(), unknown: true })
        })
    }

    fn dfs_start(&mut self, init: St<S>, trace: &[Event<Ex<S>, Re<S>, Ms<S>>]) -> Result<Dfs<S>, Violation> {
        let evs: Vec<Ev<Ex<S>, Re<S>, Ms<S>>> = trace
            .iter()
            .map(|e| match e.clone() {
                Event::Invoke { call, req } => Ev::Invoke(call, req),
                Event::Return { call, res } => Ev::Return(call, res),
                Event::Receive { msg } => Ev::Receive(msg),
            })
            .collect();
        let start = Node { state: self.states.intern(init), pending: HashedSet::new(), trail: Default::default() };
        let mut run = Dfs { evs, stack: Vec::new(), seen: HashSet::new(), deepest: 0, found: None };
        if run.evs.is_empty() {
            run.found = Some(start);
            return Ok(run);
        }
        run.seen.insert((0, start.clone()));
        let children = self.children(&start, &run.evs[0])?;
        run.stack.push(Frame { i: 0, children, tried: 0 });
        Ok(run)
    }

    /// Continues `run` for up to `budget` more candidates: `None` if the budget
    /// ran out first.
    fn dfs_resume(&mut self, run: &mut Dfs<S>, budget: usize) -> Option<Result<Node<S>, Violation>> {
        if let Some(n) = &run.found {
            return Some(Ok(n.clone()));
        }
        let mut explored = 0usize;
        while let Some(top) = run.stack.last_mut() {
            if top.tried == top.children.len() {
                run.stack.pop();
                continue;
            }
            let (advance, n) = top.children[top.tried].clone();
            top.tried += 1;
            let j = if advance { top.i + 1 } else { top.i };
            if j == run.evs.len() {
                self.stats.explored += explored;
                run.found = Some(n.clone());
                return Some(Ok(n));
            }
            if !run.seen.insert((j, n.clone())) {
                continue;
            }
            explored += 1;
            run.deepest = run.deepest.max(j);
            let children = match self.children(&n, &run.evs[j]) {
                Ok(c) => c,
                Err(v) => return Some(Err(Violation { index: j, ..v })),
            };
            run.stack.push(Frame { i: j, children, tried: 0 });
            if explored >= budget {
                self.stats.explored += explored;
                return None;
            }
        }
        self.stats.explored += explored;
        let d = run.deepest;
        let reason = "no execution of the model explains the history past this event".into();
        Some(Err(Violation { index: d, event: format!("{:?}", run.evs[d]), reason, profile: Vec::new(), unknown: false }))
    }

    /// The branches from `n` before event `e`: the event consumed, if nothing
    /// is owed before it; otherwise each single move on the keys of what is
    /// owed, in invocation order. Each says whether it consumed the event.
    fn children(&self, n: &Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<Vec<(bool, Node<S>)>, Violation> {
        let at = |v: String| Violation { index: 0, event: format!("{e:?}"), unknown: gave_up(&v), reason: v, profile: Vec::new() };
        let unsent = matches!(e, Ev::Receive(msg) if !self.has_sent(n, msg));
        if !self.owes(n, e) && !unsent {
            return Ok(self.consume(n, e).map_err(at)?.into_iter().map(|m| (true, m)).collect());
        }
        let owed: Vec<P<S>> = self.owed(n, e).into_iter().cloned().collect();
        let first = self.earliest_overdue(n);
        let relevant = if !self.cfg.footprints {
            Touches::Everything
        } else {
            let seed = match e {
                Ev::Receive(msg) => self.engine.dispatch_keys(msg),
                _ => Touches::Only(Vec::new()),
            };
            let owed_refs: Vec<&P<S>> = owed.iter().collect();
            self.relevant(n, &owed_refs, seed)
        };
        let mut items: Vec<&P<S>> = n
            .pending
            .iter()
            .filter(|item| self.can_fire(item, &n.state))
            .filter(|item| match first {
                Some(d) => matches!(item, Pending::Step { must: true, by: Some(by), .. } if *by == d) && self.is_overdue(item, &n.state),
                None => self.is_clock(item) || intersects(&relevant, &self.footprint(item, n)),
            })
            .collect();
        // Calls in the order they were invoked (call ids rise), as Porcupine
        // tries them: the call made first most often took effect first.
        // Internal work after them, earliest deadline first.
        items.sort_by_key(|item| match item {
            Pending::InFlight { call, .. } => (0, *call, 0),
            Pending::Step { by, .. } => (1, 0, by.unwrap_or(Time::MAX)),
            _ => (2, 0, 0),
        });
        let mut out = Vec::new();
        for item in items {
            // A call that never returns and would change nothing need never
            // take effect: applying it only doubles the candidates.
            if let Pending::InFlight { call, op, .. } = item {
                if self.orphans.contains(call) && read_only::<S>(&self.engine.model().external(op, &n.state), &n.state) {
                    continue;
                }
            }
            for m in self.fire_exact(n, item) {
                if m != *n {
                    out.push((false, m));
                }
            }
        }
        Ok(out)
    }

    /// [`Checker::fire`], except that a read takes effect like any call, with
    /// the answer it gets here: depth first, where it takes effect is a branch,
    /// and remembering every answer it could have had would make the same
    /// candidate look different on every path.
    fn fire_exact(&self, m: &Node<S>, item: &P<S>) -> Vec<Node<S>> {
        let Pending::InFlight { call, op, .. } = item else { return self.fire(m, item) };
        self.engine
            .model()
            .external(op, &m.state)
            .into_iter()
            .enumerate()
            .filter(|(_, o)| self.answers.get(call).is_none_or(|r| &o.resp == r))
            .map(|(j, o)| {
                let mut p = m.pending.clone();
                p.remove(item);
                p.insert(Pending::Responded { call: *call, resp: o.resp });
                self.spawn(&mut p, o.work, &o.next);
                for msg in o.send {
                    add_sent(&mut p, msg);
                }
                let trail = self.record(&m.trail, || Record::Effect { call: *call, j });
                Node { state: self.states.intern(o.next), pending: p, trail }
            })
            .collect()
    }

    /// Checks the simplest trace: calls made one after another, each answered
    /// before the next is sent. This is the shape of a log of request/response
    /// pairs, such as resonate-specification's NDJSON.
    pub fn check_calls<I>(&mut self, trace: I) -> Result<&Stats, Violation>
    where
        I: IntoIterator<Item = (Ex<S>, Re<S>)>,
    {
        for (i, (req, res)) in trace.into_iter().enumerate() {
            let call = self.next_call;
            self.next_call += 1;
            self.call(call, req, res).map_err(|v| Violation { index: i, ..v })?;
        }
        Ok(&self.stats)
    }

    /// Checks a whole trace, as [`Checker::check`] does, and backs an acceptance
    /// with a certificate, as [`Checker::certified`] does.
    pub fn check_certified<I>(&mut self, trace: I) -> Result<Certificate, Violation>
    where
        I: IntoIterator<Item = Event<Ex<S>, Re<S>, Ms<S>>>,
    {
        if self.stats.events == 0 {
            self.recording = true;
        }
        self.check(trace)?;
        self.certified()
    }

    /// A certificate for the history so far: the silent steps of the execution
    /// the search found, before each observed event. Before answering,
    /// [`certify`](crate::certify) replays them with the history. Whatever
    /// passes is valid as long as `certify` is right (proved for its Lean copy
    /// in `lean/Accordant.lean`); the search needs no proof.
    ///
    /// Needs [`Config::certify`] from the start, and one factor:
    /// [`Checker::new`] or [`Checker::with_footprints`].
    pub fn certified(&self) -> Result<Certificate, Violation> {
        let n = self.observed.len();
        let fail = |reason: String| Violation {
            index: n,
            event: "certificate".into(),
            reason: format!("{GAVE_UP}{reason}"),
            profile: Vec::new(),
            unknown: true,
        };
        if !self.recording {
            return Err(fail("a certificate needs Config::certify from the start".into()));
        }
        let cert = self.certificate().map_err(fail)?;
        match certificate::certify(self.engine.model(), self.init.clone(), &self.observed, &cert) {
            Ok(()) => Ok(cert),
            Err(k) => Err(fail(format!("certify rejects the steps up to event {k}: {:?}", cert.get(k)))),
        }
    }

    /// The silent steps of one candidate, grouped by the event they precede:
    /// what it recorded, with work named by position and each read-only call
    /// placed where it took effect.
    fn certificate(&self) -> Result<Certificate, String> {
        let node = match self.factors.as_slice() {
            [] => return Ok(Vec::new()), // nothing observed yet
            [f] if f.parts.is_none() => &f.nodes[0],
            _ => return Err("a certificate needs one factor: use Checker::new or Checker::with_footprints".into()),
        };
        let model = self.engine.model();
        let recs = node.trail.records();
        // A read-only call takes effect at the first point it could have
        // answered what it answered.
        let mut chosen = HashSet::new();
        let mut early: HashMap<CallId, Vec<(usize, Re<S>)>> = HashMap::new();
        let mut placed = HashSet::new();
        for (k, r) in recs.iter().enumerate() {
            let pick = |call: &CallId, ok: &dyn Fn(&Re<S>) -> bool| {
                early.get(call).and_then(|v| v.iter().find(|(_, r)| ok(r))).map(|(at, _)| *at)
            };
            match r {
                Record::Obs(Event::Invoke { call, .. }) => {
                    early.remove(call);
                    placed.remove(call);
                }
                Record::Effect { call, .. } => {
                    placed.insert(*call);
                }
                Record::Early { call, res, .. } => early.entry(*call).or_default().push((k, res.clone())),
                Record::Obs(Event::Return { call, res, .. }) if !placed.contains(call) => {
                    chosen.insert(pick(call, &|r| r == res).ok_or(format!("call {call}: no early answer is {res:?}"))?);
                }
                _ => {}
            }
        }
        let mut c = certificate::Config::initial(model, self.init.clone());
        let mut cert: Certificate = Vec::new();
        let mut before: Vec<Silent> = Vec::new();
        for (k, r) in recs.into_iter().enumerate() {
            let s = match r {
                Record::Obs(e) => {
                    c.observe(&e).map_err(|()| format!("event {} can't happen here: {e:?}", cert.len()))?;
                    cert.push(std::mem::take(&mut before));
                    continue;
                }
                Record::Effect { call, j } => Silent::Effect { call, j },
                Record::Early { call, j, .. } if chosen.contains(&k) => Silent::Effect { call, j },
                Record::Early { .. } => continue,
                Record::Run { work, j } => {
                    Silent::Run { i: c.work.iter().position(|w| *w == work).ok_or(format!("{work:?} is not pending"))?, j }
                }
            };
            c.silent(s).map_err(|()| format!("before event {}, the step can't be taken: {s:?}", cert.len()))?;
            before.push(s);
        }
        Ok(cert)
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
            m.pending.insert(Pending::InFlight { call: probe, op: op.clone(), early: BTreeSet::new() });
            let owed = self.owed_for(&m, Some((probe, None)));
            let relevant = if self.cfg.footprints { self.relevant(&m, &owed, Touches::Only(Vec::new())) } else { Touches::Everything };
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

    fn apply(&mut self, e: Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        let seen = match (&e, self.recording) {
            (Ev::Invoke(call, req), true) => Some(Event::Invoke { call: *call, req: req.clone() }),
            (Ev::Return(call, res), true) => Some(Event::Return { call: *call, res: res.clone() }),
            (Ev::Receive(msg), true) => Some(Event::Receive { msg: msg.clone() }),
            _ => None,
        };
        self.apply_ev(e)?;
        self.observed.extend(seen);
        Ok(())
    }

    fn apply_ev(&mut self, e: Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        let index = self.stats.events;
        self.stats.events += 1;
        if let Some((b, _, _)) = &self.broadcasting {
            if !matches!(&e, Ev::Return(call, _) if call == b) {
                // Something else is observed while the broadcast is in flight:
                // from here on it is explained in one factor that holds
                // everything, which sees its invoke first. Nothing was observed
                // in between, so the order is the observed one.
                let (b, op, at) = self.broadcasting.take().expect("checked");
                let i = self.gather(Scope::All);
                self.within(i, |c| c.observe_in(at, &Ev::Invoke(b, op)))?;
            }
        }
        match &e {
            Ev::Invoke(call, op)
                if self.engine.partitioned()
                    && self.engine.moves_clock(op)
                    && !self.factors.iter().any(|f| f.parts.is_none()) =>
            {
                // Held until the next event: its return (explained in each
                // partition on its own) or anything else (in one factor).
                self.broadcasting = Some((*call, op.clone(), index));
                Ok(())
            }
            Ev::Return(call, res) if self.broadcasting.as_ref().is_some_and(|(b, _, _)| b == call) => {
                let (_, op, at) = self.broadcasting.take().expect("checked");
                // Partitions no factor holds take the request as well.
                let model = self.engine.model();
                let rest = match model.external(&op, &self.rest).as_slice() {
                    [o] if o.work.is_empty() && o.send.is_empty() => {
                        if o.resp != *res {
                            return Err(self.violation(index, &e, "no candidate state explains this event".into()));
                        }
                        o.next.clone()
                    }
                    _ => {
                        let reason = "gave up: spec error: a broadcast request must have one outcome that starts no work and sends nothing";
                        return Err(self.violation(index, &e, reason.into()));
                    }
                };
                let saved = self.factors.clone();
                self.each_factor(at, &Ev::Invoke(*call, op))?;
                if let Err(v) = self.each_factor(index, &e) {
                    self.factors = saved;
                    return Err(v);
                }
                self.rest = rest;
                Ok(())
            }
            Ev::Invoke(call, op) => {
                let scope = self.scope(self.engine.external_keys(op));
                if let Scope::Parts(ps) = &scope {
                    if let Some(p) = ps.first() {
                        self.calls.insert(*call, p.clone());
                    }
                }
                let i = self.gather(scope);
                self.within(i, |c| c.observe_in(index, &e))
            }
            Ev::Receive(msg) => {
                let scope = self.scope(self.engine.dispatch_keys(msg));
                let i = self.gather(scope);
                self.within(i, |c| c.observe_in(index, &e))
            }
            Ev::Return(call, _) => match self.factor_of(*call) {
                Some(i) => {
                    self.within(i, |c| c.observe_in(index, &e))?;
                    self.calls.remove(call);
                    Ok(())
                }
                None => Err(self.violation(index, &e, format!("call {call} is not outstanding"))),
            },
        }
    }

    /// Explains `e` in every factor on its own. All or nothing: on a violation
    /// the factors are left as they were.
    fn each_factor(&mut self, index: usize, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        let saved = self.factors.clone();
        let mut done = Vec::new();
        for f in std::mem::take(&mut self.factors) {
            self.factors = vec![f];
            if let Err(v) = self.within(0, |c| c.observe_in(index, e)) {
                self.factors = saved;
                return Err(v);
            }
            done.append(&mut self.factors);
        }
        self.factors = done;
        Ok(())
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
                event: step,
                reason: "gave up: spec error: work reaches outside the partitions of the request or step that spawned it".into(),
                profile: Vec::new(),
                unknown: true,
            });
        }
        self.split(i);
        Ok(())
    }

    /// Splits factor `i` back into independent factors once nothing links its
    /// partitions: no pending work spans them, and its candidates are exactly the
    /// product of their projections. A merge for one request (a detached create)
    /// then lasts only as long as that request does.
    ///
    /// A factor that holds everything (after a step that touched everything,
    /// like moving the clock) splits into the partitions known so far, and the
    /// rest, which must then be the same in every candidate.
    fn split(&mut self, i: usize) {
        let global = self.factors[i].parts.is_none();
        let parts = match &self.factors[i].parts {
            Some(ps) if ps.len() >= 2 => ps.clone(),
            Some(_) => return,
            None if self.known.is_empty() => return, // no partitions at all
            None => self.known.clone(),
        };
        let nodes = &self.factors[i].nodes;
        let mut groups: Vec<BTreeSet<S::Part>> = parts.iter().map(|p| BTreeSet::from([p.clone()])).collect();
        for n in nodes {
            for item in &n.pending {
                if matches!(item, Pending::Responded { .. }) {
                    return; // answered by the spec, not yet returned: its footprint is gone
                }
                let Touches::Only(ks) = self.keys(item) else { return };
                if ks.iter().any(|k| self.engine.part(k).is_none_or(|p| !parts.contains(&p))) {
                    return; // work outside the known partitions
                }
                let touched: BTreeSet<S::Part> = ks.iter().filter_map(|k| self.engine.part(k)).collect();
                let (linked, rest): (Vec<_>, Vec<_>) = groups.into_iter().partition(|g| !g.is_disjoint(&touched));
                groups = rest;
                groups.push(linked.into_iter().flatten().collect());
            }
        }
        if groups.len() < 2 && !global {
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
                let m = Node { state, pending, trail: n.trail.clone() };
                if seen.insert(m.clone()) {
                    proj.push(m);
                }
            }
            factors.push(Factor { parts: Some(g.clone()), nodes: proj });
        }
        let product: u128 = factors.iter().map(|f| f.nodes.len() as u128).product();
        let mut rest = None;
        if global {
            let states: HashSet<St<S>> = nodes.iter().map(|n| self.engine.restrict(&n.state, &|p| !parts.contains(p))).collect();
            if states.len() != 1 {
                return; // the candidates disagree about partitions nobody touched
            }
            rest = states.into_iter().next();
        }
        if product != nodes.len() as u128 {
            return; // the candidates correlate across the groups
        }
        if let Some(r) = rest {
            self.rest = r;
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
                    self.rest.clone()
                } else {
                    self.engine.restrict(&self.rest, &|p| !claimed.contains(p))
                };
                let node = Node { state: self.states.intern(rest), pending: HashedSet::new(), trail: Default::default() };
                ((0..self.factors.len()).collect(), Factor { parts: None, nodes: vec![node] })
            }
            Scope::Parts(parts) => {
                let hit: Vec<usize> = (0..self.factors.len())
                    .filter(|&i| self.factors[i].parts.as_ref().is_some_and(|ps| !ps.is_disjoint(&parts)))
                    .collect();
                let claimed: BTreeSet<S::Part> = hit.iter().flat_map(|&i| self.factors[i].parts.iter().flatten().cloned()).collect();
                let new: BTreeSet<S::Part> = parts.difference(&claimed).cloned().collect();
                self.known.extend(new.iter().cloned());
                let state = self.engine.restrict(&self.rest, &|p| new.contains(p));
                let node = Node { state: self.states.intern(state), pending: HashedSet::new(), trail: Default::default() };
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
                out.push(Node { state: self.states.intern(state), pending, trail: x.trail.clone() });
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
    fn observe_in(&mut self, index: usize, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        self.instant(index, e)
    }

    fn instant(&mut self, index: usize, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        let mut explored = 0usize;
        let mut next = Vec::new();
        let mut seen = HashSet::new();
        for n in &self.profile {
            let found = self.explain(n.clone(), e, &mut explored).map_err(|reason| self.violation(index, e, reason))?;
            next.extend(found.into_iter().filter(|m| seen.insert(m.clone())));
        }
        self.stats.explored += explored;

        if self.cfg.subsume {
            let before = next.len();
            next = subsume::<S>(next, &|x| self.optional(x));
            self.stats.subsumed += before - next.len();
        }
        if next.is_empty() {
            return Err(self.violation(index, e, "no candidate state explains this event".into()));
        }
        if next.len() > self.cfg.max_width {
            return Err(self.violation(index, e, format!("{GAVE_UP}profile width {} exceeds max_width", next.len())));
        }
        self.profile = next;
        self.states.collect();
        Ok(())
    }

    fn violation(&self, index: usize, e: &Ev<Ex<S>, Re<S>, Ms<S>>, reason: String) -> Violation {
        Violation {
            unknown: gave_up(&reason),
            index,
            event: format!("{e:?}"),
            reason,
            profile: self.profile.iter().map(|n| format!("{n:?}")).collect(),
        }
    }

    /// Explores the fewest internal moves that let `e` be consumed from `n`: moves
    /// stop once nothing owed before `e` remains, and only work sharing a footprint
    /// with what is owed is tried. Everything else commutes past `e` and waits.
    fn explain(&self, n: Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>, explored: &mut usize) -> Result<Vec<Node<S>>, String> {
        let owed = self.owed(&n, e);
        let unsent = |m: &Node<S>| matches!(e, Ev::Receive(msg) if !self.has_sent(m, msg));
        if owed.is_empty() && !unsent(&n) {
            return self.consume(&n, e);
        }
        let relevant = if !self.cfg.footprints {
            Touches::Everything
        } else {
            let seed = match e {
                Ev::Receive(msg) => self.engine.dispatch_keys(msg),
                _ => Touches::Only(Vec::new()),
            };
            self.relevant(&n, &owed, seed)
        };
        let mut out = Vec::new();
        self.search(n, &relevant, explored, |m| {
            // Keep firing while something is owed, or the message isn't sent yet.
            if self.owes(m, e) || unsent(m) {
                return Ok(true);
            }
            out.extend(self.consume(m, e)?);
            Ok(false)
        })?;
        Ok(out)
    }

    fn has_sent(&self, m: &Node<S>, msg: &Ms<S>) -> bool {
        m.pending.iter().any(|i| matches!(i, Pending::Sent { msg: sent, .. } if sent == msg))
    }

    /// Breadth-first over moves on `relevant` keys. `visit` returns whether to keep
    /// expanding a node. Overdue work has priority: while a node has some, only
    /// the overdue work with the earliest deadline may fire, so an overdue timer
    /// is never overtaken.
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
                return Err(format!("{GAVE_UP}explored more than {} nodes", self.cfg.max_explore));
            }
            let first = self.earliest_overdue(&m);
            let m = if first.is_none() { self.saturate(m, relevant) } else { m };
            if !visit(&m)? {
                continue;
            }
            for item in &m.pending {
                if !self.can_fire(item, &m.state) {
                    continue;
                }
                match first {
                    Some(d) => {
                        let at_d = matches!(item, Pending::Step { must: true, by: Some(by), .. } if *by == d);
                        if !(at_d && self.is_overdue(item, &m.state)) {
                            continue;
                        }
                    }
                    None => {
                        if !self.is_clock(item) && !intersects(relevant, &self.footprint(item, &m)) {
                            continue;
                        }
                    }
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

    /// Fires every relevant read-only call in flight: each only adds answers it
    /// could give, so the result can do everything `m` can, and the orders in
    /// which reads could fire need not be explored one by one.
    fn saturate(&self, mut m: Node<S>, relevant: &Touches<S::Key>) -> Node<S> {
        let reads: Vec<P<S>> = m
            .pending
            .iter()
            .filter(|i| matches!(i, Pending::InFlight { .. }) && intersects(relevant, &self.keys(i)))
            .cloned()
            .collect();
        for item in reads {
            let Pending::InFlight { op, .. } = &item else { continue };
            let outs = self.engine.model().external(op, &m.state);
            if read_only::<S>(&outs, &m.state) {
                if let Some(next) = self.fire(&m, &item).pop() {
                    m = next;
                }
            }
        }
        m
    }

    /// An obligation whose deadline is now or past on the model's clock and
    /// that can fire: it must fire before anything else happens.
    fn is_overdue(&self, item: &P<S>, state: &St<S>) -> bool {
        match item {
            Pending::Step { step, must: true, by: Some(by), .. } => {
                *by <= self.engine.model().now(state) && self.enabled(item, step, state)
            }
            _ => false,
        }
    }

    /// The earliest deadline among `m`'s overdue work, if it has any. Asks the
    /// model whether work can run only in deadline order, until one can.
    fn earliest_overdue(&self, m: &Node<S>) -> Option<Time> {
        let now = self.engine.model().now(&m.state);
        let mut due: Vec<(Time, &P<S>)> = m
            .pending
            .iter()
            .filter_map(|i| match i {
                Pending::Step { must: true, by: Some(by), after, .. } if *by <= now && *after <= now => Some((*by, i)),
                _ => None,
            })
            .collect();
        due.sort_by_key(|(by, _)| *by);
        due.into_iter().find(|(_, i)| self.is_overdue(i, &m.state)).map(|(by, _)| by)
    }

    /// What must happen, at the current time, before `e` can be consumed from `m`.
    fn owed<'a>(&self, m: &'a Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Vec<&'a P<S>> {
        let returning = match e {
            Ev::Return(c, r) => Some((*c, Some(r))),
            _ => None,
        };
        self.owed_for(m, returning)
    }

    /// Whether anything is owed before `e`: [`Checker::owed`], without
    /// collecting it.
    fn owes(&self, m: &Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> bool {
        let returning = match e {
            Ev::Return(c, r) => Some((*c, r)),
            _ => None,
        };
        let call_owed = m.pending.iter().any(|item| match (item, returning) {
            (Pending::InFlight { call, early, .. }, Some((c, o))) if *call == c => {
                !early.iter().any(|r| r == o)
            }
            _ => false,
        });
        call_owed || self.earliest_overdue(m).is_some()
    }

    /// `returning`: the call being answered, and the answer if known. A call whose
    /// early answers already admit it owes nothing.
    fn owed_for<'a>(
        &self,
        m: &'a Node<S>,
        returning: Option<(CallId, Option<&Re<S>>)>,
    ) -> Vec<&'a P<S>> {
        m.pending
            .iter()
            .filter(|item| match item {
                Pending::InFlight { call, early, .. } => match returning {
                    Some((c, obs)) if c == *call => !obs.is_some_and(|o| early.iter().any(|r| r == o)),
                    _ => false,
                },
                Pending::Step { must: true, .. } => self.is_overdue(item, &m.state),
                _ => false,
            })
            .collect()
    }

    fn enabled(&self, item: &P<S>, step: &In<S>, state: &St<S>) -> bool {
        self.can_fire(item, state) && !self.engine.model().internal(step, state).is_empty()
    }

    /// The footprint of what is owed, closed over pending work that shares keys with it.
    fn relevant(&self, n: &Node<S>, owed: &[&P<S>], seed: Touches<S::Key>) -> Touches<S::Key> {
        let mut keys: BTreeSet<S::Key> = match seed {
            Touches::Everything => return Touches::Everything,
            Touches::Only(ks) => ks.into_iter().collect(),
        };
        for item in owed {
            match self.footprint(item, n) {
                Touches::Everything => return Touches::Everything,
                Touches::Only(ks) => keys.extend(ks),
            }
        }
        let mut prints = Vec::new();
        for item in n.pending.iter().filter(|i| self.can_fire(i, &n.state)) {
            match self.footprint(item, n) {
                Touches::Everything => return Touches::Everything,
                Touches::Only(ks) => prints.push(ks),
            }
        }
        loop {
            let before = keys.len();
            prints.retain(|ks| {
                if ks.iter().any(|k| keys.contains(k)) {
                    keys.extend(ks.iter().cloned());
                    false
                } else {
                    true
                }
            });
            if keys.len() == before {
                return Touches::Only(keys.into_iter().collect());
            }
        }
    }

    /// Whether `item` could fire in `state` at all: a call in flight, or a step
    /// whose time has come. Cheap, so it filters before footprints are built.
    fn can_fire(&self, item: &P<S>, state: &St<S>) -> bool {
        match item {
            Pending::InFlight { .. } => true,
            Pending::Step { after, .. } => *after <= self.engine.model().now(state),
            Pending::Responded { .. } | Pending::Sent { .. } => false,
        }
    }

    fn is_clock(&self, item: &P<S>) -> bool {
        matches!(item, Pending::InFlight { op, .. } if self.engine.moves_clock(op))
    }

    /// What firing `item` in node `n` may affect. A clock move affects the
    /// work that falls due by the time it moves to, and whatever could happen
    /// before it and would come out differently after it (a call in flight
    /// that reads the clock). Anything else affects its keys.
    fn footprint(&self, item: &P<S>, n: &Node<S>) -> Touches<S::Key> {
        let Pending::InFlight { op, .. } = item else { return self.reach(item, n) };
        if !self.engine.moves_clock(op) {
            return self.reach(item, n);
        }
        let model = self.engine.model();
        let mut keys = Vec::new();
        let others = n.pending.iter().filter(|i| *i != item && !self.is_clock(i) && self.can_fire(i, &n.state));
        for other in others.filter(|i| !self.commutes_with_clock(i, op, &n.state)) {
            match self.keys(other) {
                Touches::Everything => return Touches::Everything,
                Touches::Only(ks) => keys.extend(ks),
            }
        }
        for o in model.external(op, &n.state) {
            let to = model.now(&o.next);
            for work in &n.pending {
                if let Pending::Step { step, must: true, by: Some(by), .. } = work {
                    if *by <= to {
                        match self.engine.internal_keys(step) {
                            Touches::Everything => return Touches::Everything,
                            Touches::Only(ks) => keys.extend(ks),
                        }
                    }
                }
            }
        }
        Touches::Only(keys)
    }

    /// Whether firing `item` and then moving the clock with `clock` comes out as
    /// moving it first and then firing `item`, outcome for outcome. Work started
    /// counts as not commuting: it is timed by the clock it starts on.
    fn commutes_with_clock(&self, item: &P<S>, clock: &Ex<S>, state: &St<S>) -> bool {
        let model = self.engine.model();
        let tick = |s: &St<S>| -> Option<St<S>> {
            match model.external(clock, s).as_slice() {
                [o] if o.work.is_empty() && o.send.is_empty() => Some(o.next.clone()),
                _ => None,
            }
        };
        let Some(later) = tick(state) else { return false };
        type Seen<S> = Vec<(St<S>, Option<Re<S>>, Vec<Ms<S>>)>;
        let outcomes = |s: &St<S>| -> Option<Seen<S>> {
            match item {
                Pending::InFlight { op, .. } => model
                    .external(op, s)
                    .into_iter()
                    .map(|o| o.work.is_empty().then_some((o.next, Some(o.resp), o.send)))
                    .collect(),
                Pending::Step { step, .. } => {
                    model.internal(step, s).into_iter().map(|o| o.work.is_empty().then_some((o.next, None, o.send))).collect()
                }
                _ => None,
            }
        };
        let (Some(first), Some(mut second)) = (outcomes(state), outcomes(&later)) else { return false };
        let Some(mut first) = first.into_iter().map(|(n, r, m)| Some((tick(&n)?, r, m))).collect::<Option<Seen<S>>>() else {
            return false;
        };
        if first.len() != second.len() {
            return false;
        }
        // The same outcomes, in any order.
        for o in first.drain(..) {
            match second.iter().position(|x| *x == o) {
                Some(k) => {
                    second.swap_remove(k);
                }
                None => return false,
            }
        }
        true
    }

    /// The keys `item` touches, and those of what firing it in `n` leads to:
    /// the work its outcomes start (and the work that starts, in the state it
    /// starts in) and the dispatches they send. A static footprint can't say
    /// these: settling a promise resumes whichever tasks await it in the state.
    fn reach(&self, item: &P<S>, n: &Node<S>) -> Touches<S::Key> {
        let model = self.engine.model();
        let mut keys = match self.keys(item) {
            Touches::Everything => return Touches::Everything,
            Touches::Only(ks) => ks,
        };
        // (state, work started in it, dispatches sent, depth), followed until
        // no more is started.
        type Led<S> = (St<S>, Vec<Sched<In<S>>>, Vec<Ms<S>>, usize);
        let mut todo: Vec<Led<S>> = match item {
            Pending::InFlight { op, .. } => model.external(op, &n.state).into_iter().map(|o| (o.next, o.work, o.send, 0)).collect(),
            Pending::Step { step, .. } => model.internal(step, &n.state).into_iter().map(|o| (o.next, o.work, o.send, 0)).collect(),
            _ => return Touches::Only(keys),
        };
        while let Some((state, spawn, send, depth)) = todo.pop() {
            for msg in &send {
                match self.engine.dispatch_keys(msg) {
                    Touches::Everything => return Touches::Everything,
                    Touches::Only(ks) => keys.extend(ks),
                }
            }
            for w in spawn {
                let step = match w {
                    Sched::Later(r) | Sched::Timer(_, r) => r,
                };
                match self.engine.internal_keys(&step) {
                    Touches::Everything => return Touches::Everything,
                    Touches::Only(ks) => keys.extend(ks),
                }
                if depth >= 8 {
                    return Touches::Everything;
                }
                for o in model.internal(&step, &state) {
                    if !o.work.is_empty() || !o.send.is_empty() {
                        todo.push((o.next, o.work, o.send, depth + 1));
                    }
                }
            }
        }
        Touches::Only(keys)
    }

    fn keys(&self, item: &P<S>) -> Touches<S::Key> {
        match item {
            Pending::InFlight { op, .. } => self.engine.external_keys(op),
            Pending::Step { step, .. } => self.engine.internal_keys(step),
            Pending::Responded { .. } => Touches::Only(Vec::new()),
            Pending::Sent { msg, .. } => self.engine.dispatch_keys(msg),
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
            Pending::InFlight { call, op, early } => {
                let outs = self.engine.model().external(op, &m.state);
                if !read_only::<S>(&outs, &m.state) {
                    return outs
                        .into_iter()
                        .enumerate()
                        .map(|(j, o)| {
                            let mut p = without();
                            p.insert(Pending::Responded { call: *call, resp: o.resp });
                            self.spawn(&mut p, o.work, &o.next);
                            for msg in o.send {
                                add_sent(&mut p, msg);
                            }
                            let trail = self.record(&m.trail, || Record::Effect { call: *call, j });
                            Node { state: self.states.intern(o.next), pending: p, trail }
                        })
                        .collect();
                }
                // Linearizing here changes nothing but the answer: remember the
                // answer instead of placing the call.
                let mut seen = early.clone();
                let mut trail = m.trail.clone();
                for (j, o) in outs.into_iter().enumerate() {
                    if !seen.contains(&o.resp) {
                        trail = self.record(&trail, || Record::Early { call: *call, j, res: o.resp.clone() });
                        seen.insert(o.resp);
                    }
                }
                let mut p = without();
                p.insert(Pending::InFlight { call: *call, op: op.clone(), early: seen });
                vec![Node { state: m.state.clone(), pending: p, trail }]
            }
            Pending::Step { step, after, by, must, count } if self.can_fire(item, &m.state) => {
                self.engine
                    .model()
                    .internal(step, &m.state)
                    .into_iter()
                    .enumerate()
                    .map(|(j, s)| {
                        let mut p = without();
                        if *count > 1 {
                            // One copy runs; the others stay.
                            p.insert(Pending::Step { step: step.clone(), after: *after, by: *by, must: *must, count: count - 1 });
                        }
                        self.spawn(&mut p, s.work, &s.next);
                        for msg in s.send {
                            add_sent(&mut p, msg);
                        }
                        let trail = self.record(&m.trail, || Record::Run {
                            work: Work { req: step.clone(), after: *after, due: *by, must: *must },
                            j,
                        });
                        Node { state: self.states.intern(s.next), pending: p, trail }
                    })
                    .collect()
            }
            _ => Vec::new(),
        }
    }

    /// Starts work, on the clock of `next`, the state the starting step leads to.
    fn spawn(&self, pending: &mut HashedSet<P<S>>, steps: Vec<Sched<In<S>>>, next: &St<S>) {
        let now = self.engine.model().now(next);
        for sched in steps {
            let (step, after, by) = match sched {
                Sched::Later(step) => (step, now, None),
                Sched::Timer(at, step) => (step, at.max(now), Some(at.max(now))),
            };
            if let Some(Some(parts)) = &self.scope {
                let escaped = match self.engine.internal_keys(&step) {
                    Touches::Everything => true,
                    Touches::Only(ks) => ks.iter().any(|k| self.engine.part(k).is_none_or(|p| !parts.contains(&p))),
                };
                if escaped {
                    self.escaped.borrow_mut().get_or_insert_with(|| format!("{step:?}"));
                }
            }
            add_step(pending, step, after, by);
        }
    }

    /// Applies the observation itself. `Ok(None)` means this node cannot explain it.
    fn consume(&self, m: &Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<Vec<Node<S>>, String> {
        let mut p = m.pending.clone();
        match e {
            Ev::Invoke(call, op) => {
                let reused = p.iter().any(|i| {
                    matches!(i, Pending::InFlight { call: c, .. } | Pending::Responded { call: c, .. } if c == call)
                });
                if reused {
                    return Err(format!("call {call} invoked while still outstanding"));
                }
                p.insert(Pending::InFlight { call: *call, op: op.clone(), early: BTreeSet::new() });
            }
            Ev::Return(call, observed) => {
                let hit = p.iter().find_map(|i| match i {
                    Pending::Responded { call: c, resp } if c == call => {
                        (resp == observed).then(|| i.clone())
                    }
                    Pending::InFlight { call: c, early, .. } if c == call => {
                        early.iter().any(|r| r == observed).then(|| i.clone())
                    }
                    _ => None,
                });
                match hit {
                    Some(i) => {
                        p.remove(&i);
                    }
                    None => return Ok(Vec::new()),
                }
            }
            Ev::Receive(observed) => {
                // Any matching message may be the one received.
                return Ok(p
                    .iter()
                    .filter_map(|i| match i {
                        Pending::Sent { msg, count } if msg == observed => {
                            let mut q = p.clone();
                            q.remove(i);
                            if *count > 1 {
                                q.insert(Pending::Sent { msg: msg.clone(), count: count - 1 });
                            }
                            let trail = self.record(&m.trail, || Record::Obs(Event::Receive { msg: msg.clone() }));
                            Some(Node { state: m.state.clone(), pending: q, trail })
                        }
                        _ => None,
                    })
                    .collect());
            }
        }
        let trail = match e {
            Ev::Invoke(call, req) => self.record(&m.trail, || Record::Obs(Event::Invoke { call: *call, req: req.clone() })),
            Ev::Return(call, res) => self.record(&m.trail, || Record::Obs(Event::Return { call: *call, res: res.clone() })),
            _ => m.trail.clone(),
        };
        Ok(vec![Node { state: m.state.clone(), pending: p, trail }])
    }

    /// Work a node may simply never do, messages it may never deliver, and
    /// calls that never return: dropping them cannot add behaviors.
    fn optional(&self, item: &P<S>) -> bool {
        match item {
            Pending::InFlight { call, .. } => self.orphans.contains(call),
            _ => optional(item),
        }
    }

    fn record(&self, trail: &Tr<S>, rec: impl FnOnce() -> Rec<S>) -> Tr<S> {
        if self.recording {
            trail.push(rec())
        } else {
            trail.clone()
        }
    }
}

/// The response each call in `trace` gets; empty if a call id is invoked twice.
fn answers<X, R: Clone, D>(trace: &[Event<X, R, D>]) -> HashMap<CallId, R> {
    let mut invoked = HashSet::new();
    let mut out = HashMap::new();
    for e in trace {
        match e {
            Event::Invoke { call, .. } if !invoked.insert(*call) => return HashMap::new(),
            Event::Return { call, res } => {
                out.insert(*call, res.clone());
            }
            _ => {}
        }
    }
    out
}

/// A depth-first search in progress, resumable.
struct Dfs<S: Engine> {
    evs: Vec<Ev<Ex<S>, Re<S>, Ms<S>>>,
    stack: Vec<Frame<S>>,
    /// Every (position, candidate) explored; success returns at once, so all
    /// of them failed or are on the stack.
    seen: HashSet<(usize, Node<S>)>,
    deepest: usize,
    found: Option<Node<S>>,
}

struct Frame<S: Engine> {
    /// The event the candidates here are before.
    i: usize,
    /// Branches: whether each consumes event `i`, and where it leads.
    children: Vec<(bool, Node<S>)>,
    tried: usize,
}

/// A call whose every outcome leaves the state as it is and starts nothing.
fn read_only<S: Engine>(outs: &[crate::ExternalOutcome<S::M>], state: &St<S>) -> bool {
    outs.iter().all(|o| o.work.is_empty() && o.send.is_empty() && o.next == *state)
}

fn intersects<K: Ord>(a: &Touches<K>, b: &Touches<K>) -> bool {
    match (a, b) {
        (Touches::Everything, Touches::Only(v)) | (Touches::Only(v), Touches::Everything) => !v.is_empty(),
        (Touches::Everything, Touches::Everything) => true,
        (Touches::Only(x), Touches::Only(y)) => x.iter().any(|k| y.contains(k)),
    }
}

/// Records one more copy of a sent message.
fn add_sent<O: Data, R: Data, T: Data, G: Data>(p: &mut HashedSet<Pending<O, R, T, G>>, msg: G) {
    let have = p.iter().find_map(|i| match i {
        Pending::Sent { msg: m, count } if *m == msg => Some(*count),
        _ => None,
    });
    if let Some(n) = have {
        p.remove(&Pending::Sent { msg: msg.clone(), count: n });
    }
    p.insert(Pending::Sent { msg, count: have.unwrap_or(0) + 1 });
}

/// Starts work that must run: one more copy if the same work is pending.
fn add_step<O: Data, R: Data, T: Data, G: Data>(p: &mut HashedSet<Pending<O, R, T, G>>, step: T, after: Time, by: Option<Time>) {
    let have = p.iter().find_map(|i| match i {
        Pending::Step { step: s, after: a, by: b, must: true, count } if *s == step && *a == after && *b == by => Some(*count),
        _ => None,
    });
    if let Some(n) = have {
        p.remove(&Pending::Step { step: step.clone(), after, by, must: true, count: n });
    }
    p.insert(Pending::Step { step, after, by, must: true, count: have.unwrap_or(0) + 1 });
}

/// Work a node may simply never do, and messages it may never deliver: dropping
/// them cannot add behaviors.
fn optional<O, R, T, G>(item: &Pending<O, R, T, G>) -> bool {
    matches!(item, Pending::Step { must: false, .. } | Pending::Sent { .. })
}

/// An item with its early answers cleared, so calls compare by identity alone.
fn skeleton<O: Clone, R: Clone, T: Clone, G: Clone>(item: &Pending<O, R, T, G>) -> Pending<O, R, T, G> {
    match item {
        Pending::InFlight { call, op, .. } => Pending::InFlight { call: *call, op: op.clone(), early: BTreeSet::new() },
        _ => item.clone(),
    }
}

/// Whether node `b` can do everything node `a` can: same state and same owed
/// work, at least `a`'s optional work, and at least `a`'s early answers per call.
fn simulates<S: Engine>(b: &Node<S>, a: &Node<S>, optional: &dyn Fn(&P<S>) -> bool) -> bool {
    a.pending.iter().all(|x| match x {
        Pending::InFlight { call, early, .. } => b.pending.iter().any(|y| {
            matches!(y, Pending::InFlight { call: c, early: e, .. } if c == call && early.is_subset(e))
        }),
        _ if optional(x) => b.pending.contains(x),
        _ => true,
    })
}

/// Keeps only nodes no other node simulates.
fn subsume<S: Engine>(nodes: Vec<Node<S>>, optional: &dyn Fn(&P<S>) -> bool) -> Vec<Node<S>> {
    type Group<S> = (Interned<St<S>>, Vec<P<S>>);
    let mut groups: HashMap<Group<S>, Vec<usize>> = HashMap::new();
    for (i, n) in nodes.iter().enumerate() {
        let owed: Vec<_> = n.pending.iter().filter(|x| !optional(x)).map(skeleton).collect();
        groups.entry((n.state.clone(), owed)).or_default().push(i);
    }
    let mut keep = vec![true; nodes.len()];
    for idx in groups.values().filter(|g| g.len() > 1) {
        for &a in idx {
            for &b in idx {
                if a != b && keep[b] && simulates(&nodes[b], &nodes[a], optional) {
                    keep[a] = false;
                    break;
                }
            }
        }
    }
    nodes.into_iter().zip(keep).filter_map(|(n, k)| k.then_some(n)).collect()
}
