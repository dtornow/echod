use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::certificate::{self, Certificate, Silent};
use crate::hashed_set::HashedSet;
use crate::intern::{Interned, Interner};
use crate::{CallId, Data, Engine, Event, Footprint, Grouped, Keyed, Touches, Model, Partitioned, Plain, Sched, Time};

type St<S> = <<S as Engine>::M as Model>::State;
type Ex<S> = <<S as Engine>::M as Model>::External;
type Re<S> = <<S as Engine>::M as Model>::Response;
type In<S> = <<S as Engine>::M as Model>::Internal;
type Ms<S> = <<S as Engine>::M as Model>::Dispatch;

/// What a node still carries. Sorted, so a node's identity is canonical.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Pending<O, R, T, G> {
    /// An external op invoked, not yet settled. It may settle at any point
    /// until its `Return`, or never if no `Return` comes. `early`: answers it
    /// could already have gotten by settling at an earlier point where it
    /// would not have changed the state. Reads accumulate here instead of
    /// branching the profile.
    External { call: CallId, req: O, early: BTreeSet<R> },
    /// Settled; the spec predicted `resp`, which the `Return` must match.
    Settled { call: CallId, resp: R },
    /// A message the server sent and the client has not received yet, `count`
    /// times over. It may be received later, or never.
    Sent { msg: G, count: u32 },
    /// An internal op scheduled, `count` times over: started twice, it runs
    /// twice. A timer is owed at its time; a `Later` runs when an observation
    /// needs it, or never.
    Internal { sched: Sched<T>, count: u32 },
}

type P<S> = Pending<Ex<S>, Re<S>, In<S>, Ms<S>>;

/// What a candidate did, recorded while certificates are on. The checker's
/// own view of a move: by value, before positions and early answers are
/// resolved into [`Move`]s.
#[derive(Clone, Debug)]
enum Record<O, R, T, G> {
    Obs(Event<O, R, G>),
    Effect { call: CallId, j: usize },
    /// A read-only call could settle here with outcome `j`, answering `res`.
    Early { call: CallId, j: usize, res: R },
    Run { sched: Sched<T>, j: usize },
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

/// What the checker steps on internally: the observations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Ev<O, R, G> {
    Invoke(CallId, O),
    Return(CallId, R),
    /// The client received a message the server sent on its own.
    Receive(G),
    /// The system's clock now reads this.
    Clock(Time),
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
    /// The state of partitions no factor holds: initial.
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
    /// The system's clock: moved by [`Event::Clock`], the same for every
    /// candidate, since only an observation moves it.
    now: Time,
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
    /// The model's own simulation order on states, if it has one: see
    /// [`Checker::dominating`].
    dominance: Option<Box<dyn Fn(&St<S>, &St<S>) -> bool>>,
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
            now: 0,
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
            dominance: None,
            stats: Stats { max_width: 1, ..Stats::default() },
        }
    }

    /// Subsume by the model's own order too: `dominates(b, a)` says state `b`
    /// can show every observation state `a` can, under the same pending work,
    /// so a candidate in `a` is dropped when one in `b` stands beside it. The
    /// model vouches for the order; a wrong one costs completeness (a trace the
    /// model admits is refused), never soundness (an accepted trace still has
    /// its execution). Typical: a state differing only in when internal work
    /// may next run, the earlier one dominating, since "from then on" includes
    /// every later instant.
    pub fn dominating(mut self, dominates: impl Fn(&St<S>, &St<S>) -> bool + 'static) -> Self {
        self.dominance = Some(Box::new(dominates));
        self
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

    /// Actions worth trying next, with why: the model's suggestions for every
    /// state the system may be in (at most `limit` states), each once. For a
    /// fuzz driver: the checker knows what the server may have done; the model
    /// knows what is interesting to do then.
    pub fn suggestions(&self, limit: usize) -> Vec<(crate::Action<Ex<S>>, &'static str)>
    where
        S::M: crate::Explore,
        Ex<S>: PartialEq,
    {
        use crate::Explore;
        let mut out: Vec<(crate::Action<Ex<S>>, &'static str)> = Vec::new();
        for s in self.states().take(limit) {
            for x in self.engine.model().suggest(&s, self.now) {
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
            Event::Clock { at } => Ev::Clock(at),
        })
    }

    /// The system's clock moved to `at`.
    pub fn clock(&mut self, at: Time) -> Result<(), Violation> {
        self.apply(Ev::Clock(at))
    }

    /// The system's clock as the trace last reported it.
    pub fn now(&self) -> Time {
        self.now
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
        let saved = (self.factors.clone(), self.observed.len());
        let r = self.invoke(call, req).and_then(|_| self.ret(call, res));
        if r.is_err() {
            self.factors = saved.0;
            self.observed.truncate(saved.1);
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
                Event::Receive { .. } | Event::Clock { .. } => {}
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
        self.now = trace.iter().fold(self.now, |now, e| if let Event::Clock { at } = e { *at } else { now });
        self.factors = vec![Factor { parts: None, nodes: vec![node] }];
        if self.recording {
            self.observed = trace.to_vec();
        }
        self.stats.events += trace.len();
        Ok(&self.stats)
    }

    /// The history's events grouped by the one partition each stays in, with
    /// their positions; `None` if some event spans partitions or is a clock move.
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
                Event::Clock { .. } => return None,
                Event::Invoke { call, req } => {
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
                Event::Clock { at } => Ev::Clock(at),
            })
            .collect();
        // The clock before each event: a depth-first search visits positions
        // out of order, so the checker's clock is set per position.
        let mut clocks = Vec::with_capacity(evs.len());
        let mut now = self.now;
        for e in &evs {
            clocks.push(now);
            if let Ev::Clock(at) = e {
                now = *at;
            }
        }
        let start = Node { state: self.states.intern(init), pending: HashedSet::new(), trail: Default::default() };
        let mut run = Dfs { evs, clocks, stack: Vec::new(), seen: HashSet::new(), deepest: 0, found: None };
        if run.evs.is_empty() {
            run.found = Some(start);
            return Ok(run);
        }
        run.seen.insert((0, start.clone()));
        self.now = run.clocks[0];
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
            self.now = run.clocks[j];
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
        let clock = matches!(e, Ev::Clock(_));
        let mut out = Vec::new();
        if !self.owes(n, e) && !unsent {
            out.extend(self.consume(n, e).map_err(at)?.into_iter().map(|m| (true, m)));
            if !clock {
                return Ok(out);
            }
            // A clock move may also come after work it doesn't commute with.
        }
        let owed: Vec<P<S>> = self.owed(n, e).into_iter().cloned().collect();
        let first = self.earliest_overdue(n);
        let relevant = if !self.cfg.footprints {
            Touches::Everything
        } else {
            let seed = match e {
                Ev::Receive(msg) => self.engine.dispatch_keys(msg),
                Ev::Clock(to) => self.clock_seed(n, *to),
                _ => Touches::Only(Vec::new()),
            };
            let owed_refs: Vec<&P<S>> = owed.iter().collect();
            self.relevant(n, &owed_refs, seed)
        };
        let mut items: Vec<&P<S>> = n
            .pending
            .iter()
            .filter(|item| self.can_fire(item))
            .filter(|item| match first {
                Some(d) => item_due(item) == Some(d) && self.is_overdue(item, &n.state),
                None => intersects(&relevant, &self.footprint(item, n)),
            })
            .collect();
        // Calls in the order they were invoked (call ids rise), as Porcupine
        // tries them: the call made first most often took effect first.
        // Internal work after them, earliest deadline first.
        items.sort_by_key(|item| match item {
            Pending::External { call, .. } => (0, *call, 0),
            Pending::Internal { sched, .. } => (1, 0, sched.due().unwrap_or(Time::MAX)),
            _ => (2, 0, 0),
        });
        for item in items {
            // A call that never returns and would change nothing need never
            // take effect: applying it only doubles the candidates.
            if let Pending::External { call, req, .. } = item {
                if self.orphans.contains(call) && read_only::<S>(&self.engine.model().external(req, &n.state, self.now), &n.state) {
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
        let Pending::External { call, req, .. } = item else { return self.fire(m, item) };
        self.engine
            .model()
            .external(req, &m.state, self.now)
            .into_iter()
            .enumerate()
            .filter(|(_, o)| self.answers.get(call).is_none_or(|r| &o.resp == r))
            .map(|(j, o)| {
                let mut p = m.pending.clone();
                p.remove(item);
                p.insert(Pending::Settled { call: *call, resp: o.resp });
                self.spawn(&mut p, o.work);
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
    /// passes is valid: `certify` is verified (`src/certificate.rs`, against
    /// `src/semantics.rs`); the search needs no proof.
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
                Record::Run { sched, j } => {
                    Silent::Run { i: c.internals.iter().position(|w| *w == sched).ok_or(format!("{sched:?} is not pending"))?, j }
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
            m.pending.insert(Pending::External { call: probe, req: op.clone(), early: BTreeSet::new() });
            let owed = self.owed_for(&m, Some((probe, None)));
            let relevant = if self.cfg.footprints { self.relevant(&m, &owed, Touches::Only(Vec::new())) } else { Touches::Everything };
            let _ = self.search(m, &relevant, &mut explored, |_, x| {
                for i in &x.pending {
                    let found: Vec<&Re<S>> = match i {
                        Pending::Settled { call, resp } if *call == probe => vec![resp],
                        Pending::External { call, early, .. } if *call == probe => early.iter().collect(),
                        _ => continue,
                    };
                    for r in found {
                        if !out.contains(r) {
                            out.push(r.clone());
                        }
                    }
                }
                Ok(x.pending.iter().any(|i| matches!(i, Pending::External { call, .. } if *call == probe)))
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
            (Ev::Clock(at), true) => Some(Event::Clock { at: *at }),
            _ => None,
        };
        self.apply_ev(e)?;
        self.observed.extend(seen);
        Ok(())
    }

    fn apply_ev(&mut self, e: Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        let index = self.stats.events;
        self.stats.events += 1;
        match &e {
            Ev::Clock(at) => {
                if *at < self.now {
                    return Err(self.violation(index, &e, format!("the clock moves back, from {} to {at}", self.now)));
                }
                // Explained in every factor on its own: overdue work runs
                // first in each, then the clock moves for all. With nothing
                // observed yet there is nothing pending, and a partitioned
                // checker must not merge its partitions into one factor over it.
                if !self.factors.is_empty() {
                    self.each_factor(index, &e)?;
                } else if !self.engine.partitioned() {
                    let i = self.gather(Scope::All);
                    self.within(i, |c| c.observe_in(index, &e))?;
                }
                self.now = *at;
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
                if matches!(item, Pending::Settled { .. }) {
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
                    matches!(i, Pending::External { call: c, .. } | Pending::Settled { call: c, .. } if *c == call)
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
            next = subsume::<S>(next, &|x| self.optional(x), self.dominance.as_deref());
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
        if let Ev::Clock(at) = e {
            // A clock move doesn't commute with work it changes: the move
            // may come after any number of such moves, each a candidate.
            let relevant = if !self.cfg.footprints { Touches::Everything } else { self.relevant(&n, &owed, self.clock_seed(&n, *at)) };
            let mut out = Vec::new();
            self.search(n, &relevant, explored, |_, m| {
                if !self.owes(m, e) {
                    out.extend(self.consume(m, e)?);
                }
                Ok(true)
            })?;
            return Ok(out);
        }
        // The call a return answers: it may take effect later than an early
        // answer places it (below), so its keys are always relevant.
        let returning: Option<(&CallId, &Re<S>, P<S>)> = match e {
            Ev::Return(call, res) => n
                .pending
                .iter()
                .find(|i| matches!(i, Pending::External { call: c, .. } if c == call))
                .map(|i| (call, res, i.clone())),
            _ => None,
        };
        if owed.is_empty() && !unsent(&n) && returning.is_none() {
            return self.consume(&n, e);
        }
        let relevant = if !self.cfg.footprints {
            Touches::Everything
        } else {
            let seed = match e {
                Ev::Receive(msg) => self.engine.dispatch_keys(msg),
                _ => Touches::Only(Vec::new()),
            };
            let mut owed = owed;
            if let Some((_, _, item)) = &returning {
                if !owed.contains(&item) {
                    owed.push(item);
                }
            }
            self.relevant(&n, &owed, seed)
        };
        let mut out = Vec::new();
        let admitted = |m: &Node<S>| {
            returning.as_ref().is_some_and(|(call, res, _)| {
                m.pending.iter().any(|i| matches!(i, Pending::External { call: c, early, .. } if c == *call && early.contains(*res)))
            })
        };
        self.search(n, &relevant, explored, |parent, m| {
            // Keep firing while something is owed, or the message isn't sent yet.
            if self.owes(m, e) || unsent(m) {
                return Ok(true);
            }
            // A return an early answer admits may also be the call taking
            // effect later: a request that changes nothing in the state it was
            // first tried in (a create of an id that exists, a halt of a halted
            // task) and would change something after other work on its keys,
            // with the same answer. Both are candidates, so the search goes on
            // until the call is placed. Work fired in between commutes past the
            // return, so an early answer counts where it first admits it: at
            // the root, after work that was owed, or where the node fired from
            // did not admit it yet.
            if admitted(m) {
                let fresh = parent.is_none_or(|p| self.owes(p, e) || unsent(p) || !admitted(p));
                if fresh {
                    out.extend(self.consume(m, e)?);
                }
                return Ok(true);
            }
            out.extend(self.consume(m, e)?);
            Ok(false)
        })?;
        Ok(out)
    }

    /// What a clock move to `at` doesn't commute with: work falling due by
    /// `at`, and anything that could fire now and would come out differently
    /// after the move (its outcomes depend on the time, or it starts work,
    /// which is timed by the clock it starts on). Closed over shared keys by
    /// [`Checker::relevant`], this is what may have to fire before the move.
    fn clock_seed(&self, n: &Node<S>, at: Time) -> Touches<S::Key> {
        let model = self.engine.model();
        let mut keys = Vec::new();
        // Whether another item that can fire shares a key with `item`: what
        // `item` does may then depend on the time once that other one has
        // fired, though it doesn't now (a create of a schedule that exists,
        // with its delete in flight).
        let shared = |item: &P<S>| {
            let mine = self.keys(item);
            n.pending.iter().any(|other| !std::ptr::eq(other, item) && self.can_fire(other) && intersects(&mine, &self.keys(other)))
        };
        for item in &n.pending {
            let differs = match item {
                Pending::Internal { sched: Sched::Timer(t, _), .. } if *t <= at => true,
                Pending::External { req, .. } => {
                    let (a, b) = (model.external(req, &n.state, self.now), model.external(req, &n.state, at));
                    a.len() != b.len()
                        || a.iter().zip(&b).any(|(x, y)| !x.work.is_empty() || x.next != y.next || x.resp != y.resp || x.send != y.send)
                        || (!read_only::<S>(&a, &n.state) && shared(item))
                }
                Pending::Internal { sched, .. } if self.can_fire(item) => {
                    let (a, b) = (model.internal(sched.req(), &n.state, self.now), model.internal(sched.req(), &n.state, at));
                    a.len() != b.len() || a.iter().zip(&b).any(|(x, y)| !x.work.is_empty() || x.next != y.next || x.send != y.send)
                }
                _ => false,
            };
            if differs {
                match self.keys(item) {
                    Touches::Everything => return Touches::Everything,
                    Touches::Only(ks) => keys.extend(ks),
                }
            }
        }
        Touches::Only(keys)
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
        mut visit: impl FnMut(Option<&Node<S>>, &Node<S>) -> Result<bool, String>,
    ) -> Result<(), String> {
        let mut visited: HashSet<Node<S>> = HashSet::from([n.clone()]);
        let mut queue: VecDeque<(Option<Node<S>>, Node<S>)> = VecDeque::from([(None, n)]);
        while let Some((parent, m)) = queue.pop_front() {
            *explored += 1;
            if *explored > self.cfg.max_explore {
                return Err(format!("{GAVE_UP}explored more than {} nodes", self.cfg.max_explore));
            }
            let first = self.earliest_overdue(&m);
            let m = if first.is_none() { self.saturate(m, relevant) } else { m };
            // `visit` sees the node fired from (as visited: saturated) and this one.
            if !visit(parent.as_ref(), &m)? {
                continue;
            }
            for item in &m.pending {
                if !self.can_fire(item) {
                    continue;
                }
                match first {
                    Some(d) => {
                        let at_d = item_due(item) == Some(d);
                        if !(at_d && self.is_overdue(item, &m.state)) {
                            continue;
                        }
                    }
                    None => {
                        if !intersects(relevant, &self.footprint(item, &m)) {
                            continue;
                        }
                    }
                }
                for m2 in self.fire(&m, item) {
                    if visited.insert(m2.clone()) {
                        queue.push_back((Some(m.clone()), m2));
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
            .filter(|i| matches!(i, Pending::External { .. }) && intersects(relevant, &self.keys(i)))
            .cloned()
            .collect();
        for item in reads {
            let Pending::External { req, .. } = &item else { continue };
            let outs = self.engine.model().external(req, &m.state, self.now);
            if read_only::<S>(&outs, &m.state) {
                if let Some(next) = self.fire(&m, &item).pop() {
                    m = next;
                }
            }
        }
        m
    }

    /// An obligation whose deadline is now or past on the clock and
    /// that can fire: it must fire before anything else happens.
    fn is_overdue(&self, item: &P<S>, state: &St<S>) -> bool {
        match item {
            Pending::Internal { sched: sched @ Sched::Timer(t, _), .. } => *t <= self.now && self.enabled(item, sched.req(), state),
            _ => false,
        }
    }

    /// The earliest deadline among `m`'s overdue work, if it has any. Asks the
    /// model whether work can run only in deadline order, until one can.
    fn earliest_overdue(&self, m: &Node<S>) -> Option<Time> {
        let now = self.now;
        let mut due: Vec<(Time, &P<S>)> = m
            .pending
            .iter()
            .filter_map(|i| match i {
                Pending::Internal { sched: Sched::Timer(t, _), .. } if *t <= now => Some((*t, i)),
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
            (Pending::External { call, early, .. }, Some((c, o))) if *call == c => {
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
                Pending::External { call, early, .. } => match returning {
                    Some((c, obs)) if c == *call => !obs.is_some_and(|o| early.iter().any(|r| r == o)),
                    _ => false,
                },
                Pending::Internal { .. } => self.is_overdue(item, &m.state),
                _ => false,
            })
            .collect()
    }

    fn enabled(&self, item: &P<S>, step: &In<S>, state: &St<S>) -> bool {
        self.can_fire(item) && !self.engine.model().internal(step, state, self.now).is_empty()
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
        for item in n.pending.iter().filter(|i| self.can_fire(i)) {
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
    fn can_fire(&self, item: &P<S>) -> bool {
        match item {
            Pending::External { .. } => true,
            Pending::Internal { sched, .. } => sched.ready(self.now),
            Pending::Settled { .. } | Pending::Sent { .. } => false,
        }
    }

    /// What firing `item` in node `n` may affect: its keys and what it leads to.
    fn footprint(&self, item: &P<S>, n: &Node<S>) -> Touches<S::Key> {
        self.reach(item, n)
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
            Pending::External { req, .. } => model.external(req, &n.state, self.now).into_iter().map(|o| (o.next, o.work, o.send, 0)).collect(),
            Pending::Internal { sched, .. } => model.internal(sched.req(), &n.state, self.now).into_iter().map(|o| (o.next, o.work, o.send, 0)).collect(),
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
                for o in model.internal(&step, &state, self.now) {
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
            Pending::External { req, .. } => self.engine.external_keys(req),
            Pending::Internal { sched, .. } => self.engine.internal_keys(sched.req()),
            Pending::Settled { .. } => Touches::Only(Vec::new()),
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
            Pending::External { call, req, early } => {
                let outs = self.engine.model().external(req, &m.state, self.now);
                if !read_only::<S>(&outs, &m.state) {
                    return outs
                        .into_iter()
                        .enumerate()
                        .map(|(j, o)| {
                            let mut p = without();
                            p.insert(Pending::Settled { call: *call, resp: o.resp });
                            self.spawn(&mut p, o.work);
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
                p.insert(Pending::External { call: *call, req: req.clone(), early: seen });
                vec![Node { state: m.state.clone(), pending: p, trail }]
            }
            Pending::Internal { sched, count } if self.can_fire(item) => {
                self.engine
                    .model()
                    .internal(sched.req(), &m.state, self.now)
                    .into_iter()
                    .enumerate()
                    .map(|(j, s)| {
                        let mut p = without();
                        if *count > 1 {
                            // One copy runs; the others stay.
                            p.insert(Pending::Internal { sched: sched.clone(), count: count - 1 });
                        }
                        self.spawn(&mut p, s.work);
                        for msg in s.send {
                            add_sent(&mut p, msg);
                        }
                        let trail = self.record(&m.trail, || Record::Run { sched: sched.clone(), j });
                        Node { state: self.states.intern(s.next), pending: p, trail }
                    })
                    .collect()
            }
            _ => Vec::new(),
        }
    }

    /// Starts internal ops, on the clock as it reads now.
    fn spawn(&self, pending: &mut HashedSet<P<S>>, steps: Vec<Sched<In<S>>>) {
        for sched in steps {
            let sched = sched.at(self.now);
            if let Some(Some(parts)) = &self.scope {
                let escaped = match self.engine.internal_keys(sched.req()) {
                    Touches::Everything => true,
                    Touches::Only(ks) => ks.iter().any(|k| self.engine.part(k).is_none_or(|p| !parts.contains(&p))),
                };
                if escaped {
                    self.escaped.borrow_mut().get_or_insert_with(|| format!("{:?}", sched.req()));
                }
            }
            add_internal(pending, sched);
        }
    }

    /// Applies the observation itself. `Ok(None)` means this node cannot explain it.
    fn consume(&self, m: &Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<Vec<Node<S>>, String> {
        let mut p = m.pending.clone();
        match e {
            Ev::Invoke(call, op) => {
                let reused = p.iter().any(|i| {
                    matches!(i, Pending::External { call: c, .. } | Pending::Settled { call: c, .. } if c == call)
                });
                if reused {
                    return Err(format!("call {call} invoked while still outstanding"));
                }
                p.insert(Pending::External { call: *call, req: op.clone(), early: BTreeSet::new() });
            }
            Ev::Return(call, observed) => {
                let hit = p.iter().find_map(|i| match i {
                    Pending::Settled { call: c, resp } if c == call => {
                        (resp == observed).then(|| i.clone())
                    }
                    Pending::External { call: c, early, .. } if c == call => {
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
            Ev::Clock(_) => {}
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
            Ev::Clock(at) => self.record(&m.trail, || Record::Obs(Event::Clock { at: *at })),
            _ => m.trail.clone(),
        };
        Ok(vec![Node { state: m.state.clone(), pending: p, trail }])
    }

    /// dropping them cannot add behaviors.
    fn optional(&self, item: &P<S>) -> bool {
        match item {
            Pending::External { call, .. } => self.orphans.contains(call),
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
    /// The clock before each event.
    clocks: Vec<Time>,
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

/// Starts an internal op: one more copy if the same op is pending.
fn add_internal<O: Data, R: Data, T: Data, G: Data>(p: &mut HashedSet<Pending<O, R, T, G>>, sched: Sched<T>) {
    let have = p.iter().find_map(|i| match i {
        Pending::Internal { sched: s, count } if *s == sched => Some(*count),
        _ => None,
    });
    if let Some(n) = have {
        p.remove(&Pending::Internal { sched: sched.clone(), count: n });
    }
    p.insert(Pending::Internal { sched, count: have.unwrap_or(0) + 1 });
}

/// The time an item is owed by: a timer's. Nothing else is owed.
fn item_due<O, R, T, G>(item: &Pending<O, R, T, G>) -> Option<Time> {
    match item {
        Pending::Internal { sched, .. } => sched.due(),
        _ => None,
    }
}

/// Messages a node may never deliver: dropping them cannot add behaviors.
/// An item with its early answers cleared, so calls compare by identity alone.
fn skeleton<O: Clone, R: Clone, T: Clone, G: Clone>(item: &Pending<O, R, T, G>) -> Pending<O, R, T, G> {
    match item {
        Pending::External { call, req, .. } => Pending::External { call: *call, req: req.clone(), early: BTreeSet::new() },
        _ => item.clone(),
    }
}

/// Work a node may run or leave forever: a `Later` item (it runs when an
/// observation needs it, or never), a sent message (received, or never).
/// Holding more of it is holding more options, so a node with a superset
/// simulates one with a subset, all else equal.
fn optional<O, R, T, G>(item: &Pending<O, R, T, G>) -> bool {
    matches!(item, Pending::Sent { .. } | Pending::Internal { sched: Sched::Later(_), .. })
}

/// Whether node `b` can do everything node `a` can, given the same owed work
/// (the caller's grouping): at least `a`'s optional work, copy for copy, and at
/// least `a`'s early answers per call.
fn simulates<S: Engine>(b: &Node<S>, a: &Node<S>, optional: &dyn Fn(&P<S>) -> bool) -> bool {
    a.pending.iter().all(|x| match x {
        Pending::External { call, early, .. } => b.pending.iter().any(|y| {
            matches!(y, Pending::External { call: c, early: e, .. } if c == call && early.is_subset(e))
        }),
        _ if optional(x) => b.pending.contains(x) || b.pending.iter().any(|y| more_of(y, x)),
        _ => true,
    })
}

/// Whether `y` is `x` with more copies.
fn more_of<O: PartialEq, R, T: PartialEq, G: PartialEq>(y: &Pending<O, R, T, G>, x: &Pending<O, R, T, G>) -> bool {
    match (y, x) {
        (Pending::Sent { msg: m, count: c }, Pending::Sent { msg: n, count: d }) => m == n && c >= d,
        (Pending::Internal { sched: s, count: c }, Pending::Internal { sched: t, count: d }) => s == t && c >= d,
        _ => false,
    }
}

/// Keeps only nodes no other node simulates. Nodes are compared on the work
/// they owe; with `dominates`, a node whose state the model says dominates
/// another's simulates it too.
fn subsume<S: Engine>(nodes: Vec<Node<S>>, optional: &dyn Fn(&P<S>) -> bool, dominates: Option<&dyn Fn(&St<S>, &St<S>) -> bool>) -> Vec<Node<S>> {
    type Group<S> = (Option<Interned<St<S>>>, Vec<P<S>>);
    let mut groups: HashMap<Group<S>, Vec<usize>> = HashMap::new();
    for (i, n) in nodes.iter().enumerate() {
        let owed: Vec<_> = n.pending.iter().filter(|x| !optional(x)).map(skeleton).collect();
        // under a dominance order, states compare pairwise rather than by identity
        let state = if dominates.is_some() { None } else { Some(n.state.clone()) };
        groups.entry((state, owed)).or_default().push(i);
    }
    let same_or_dominates = |b: &Node<S>, a: &Node<S>| b.state == a.state || dominates.is_some_and(|d| d(&b.state, &a.state));
    let mut keep = vec![true; nodes.len()];
    for idx in groups.values().filter(|g| g.len() > 1) {
        for &a in idx {
            for &b in idx {
                if a != b && keep[b] && same_or_dominates(&nodes[b], &nodes[a]) && simulates(&nodes[b], &nodes[a], optional) {
                    keep[a] = false;
                    break;
                }
            }
        }
    }
    nodes.into_iter().zip(keep).filter_map(|(n, k)| k.then_some(n)).collect()
}
