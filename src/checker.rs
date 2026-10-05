use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::certificate::{self, Move, MoveOf, Work};
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
    /// Invoked at `since`, not yet linearized. It may take effect at any point
    /// until its `Return`, or never if no `Return` comes. `must`: this branch has
    /// committed to it taking effect before its request lifetime ends.
    /// `early`: answers it could already have gotten by linearizing at an earlier
    /// point where it would not have changed the state. Reads accumulate here
    /// instead of branching the profile.
    InFlight { call: CallId, op: O, since: Time, must: bool, early: BTreeSet<R> },
    /// Linearized; the spec predicted `resp`, which the `Return` must match.
    Responded { call: CallId, resp: R },
    /// A message the server sent and the client has not received yet, `count`
    /// times over. It may be received later, or never.
    Sent { msg: G, count: u32 },
    /// Background work, due from `after`. `must`: owed by `by`, or by the next
    /// `Quiesce` if `by` is `None`.
    Step { step: T, after: Time, by: Option<Time>, must: bool },
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
    /// The call took effect with an early answer `res`, at the point it was found.
    Commit { call: CallId, res: R },
    Run { work: Work<T>, j: usize },
    Advance(Time),
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

/// What a client observes, and when.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event<X, R, D> {
    /// The client sent a request.
    Invoke { at: Time, call: CallId, req: X },
    /// The client got the response to that call.
    Return { at: Time, call: CallId, res: R },
    /// The client got a dispatch the server sent on its own.
    Receive { at: Time, msg: D },
}

impl<X, R, D> Event<X, R, D> {
    pub fn at(&self) -> Time {
        match self {
            Event::Invoke { at, .. } | Event::Return { at, .. } | Event::Receive { at, .. } => *at,
        }
    }
}

/// What the checker steps on internally: observations at the current time,
/// plus time passing and the idle assertion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Ev<O, R, G> {
    Invoke(CallId, O),
    Return(CallId, R),
    /// The client received a message the server sent on its own.
    Receive(G),
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
    /// Record each candidate's moves, so [`Checker::certified`] can back the
    /// verdict with a certificate. Costs memory proportional to the history.
    pub certify: bool,
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
        let now = cfg.start;
        let recording = cfg.certify;
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
            next_call: 1 << 62,
            recording,
            observed: Vec::new(),
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
        acc.unwrap_or_else(|| vec![Node { state: self.states.intern(self.init.clone()), pending: HashedSet::new(), trail: Default::default() }])
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

    /// One observation. The clock first advances to the observation's time;
    /// times must not go backwards.
    pub fn observe(&mut self, e: Event<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        let at = e.at();
        if at < self.now {
            let index = self.stats.events;
            return Err(self.violation(index, &Ev::Tick(at), format!("observed at {at}, after time {}", self.now)));
        }
        if at > self.now {
            self.tick(at)?;
        }
        self.apply(match e {
            Event::Invoke { call, req, .. } => Ev::Invoke(call, req),
            Event::Return { call, res, .. } => Ev::Return(call, res),
            Event::Receive { msg, .. } => Ev::Receive(msg),
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

    /// Advances the clock without an observation.
    pub fn tick(&mut self, to: Time) -> Result<(), Violation> {
        self.apply(Ev::Tick(to))
    }

    /// Asserts the system is idle now: all internal work that must happen has
    /// happened, whether or not it had a deadline. Not an observation: an
    /// assumption the tester adds, for example after waiting long enough.
    pub fn assert_idle(&mut self) -> Result<(), Violation> {
        self.apply(Ev::Quiesce)
    }

    /// A call whose request and response are observed now.
    /// Atomic: if the response is rejected, the checker is left as it was.
    pub fn call(&mut self, call: CallId, req: Ex<S>, res: Re<S>) -> Result<(), Violation> {
        let saved = (self.factors.clone(), self.now, self.observed.len());
        let r = self.invoke(call, req).and_then(|_| self.ret(call, res));
        if r.is_err() {
            (self.factors, self.now) = (saved.0, saved.1);
            self.observed.truncate(saved.2);
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

    /// Checks the simplest trace: calls made one after another, each answered
    /// before the next is sent, with the time of each. This is the shape of a
    /// log of request/response pairs, such as resonate-specification's NDJSON.
    pub fn check_calls<I>(&mut self, trace: I) -> Result<&Stats, Violation>
    where
        I: IntoIterator<Item = (Time, Ex<S>, Re<S>)>,
    {
        for (i, (at, req, res)) in trace.into_iter().enumerate() {
            let call = self.next_call;
            self.next_call += 1;
            let one = [Event::Invoke { at, call, req }, Event::Return { at, call, res }];
            let saved = (self.factors.clone(), self.now, self.observed.len());
            if let Err(v) = one.into_iter().try_for_each(|e| self.observe(e)) {
                (self.factors, self.now) = (saved.0, saved.1);
                self.observed.truncate(saved.2);
                return Err(Violation { index: i, ..v });
            }
        }
        Ok(&self.stats)
    }

    /// Checks a whole trace, as [`Checker::check`] does, and backs an acceptance
    /// with a certificate, as [`Checker::certified`] does.
    pub fn check_certified<I>(&mut self, trace: I) -> Result<Vec<MoveOf<S::M>>, Violation>
    where
        I: IntoIterator<Item = Event<Ex<S>, Re<S>, Ms<S>>>,
    {
        if self.stats.events == 0 {
            self.recording = true;
        }
        self.check(trace)?;
        self.certified()
    }

    /// A certificate for the history so far: the execution the search found, as
    /// moves. Before answering, [`certify`](crate::certify) replays the moves,
    /// which must show exactly what was observed. Whatever passes is valid as
    /// long as `certify` is right (proved for its Lean copy in
    /// `lean/Accordant.lean`); the search needs no proof.
    ///
    /// Needs [`Config::certify`] from the start, and one factor:
    /// [`Checker::new`] or [`Checker::with_footprints`].
    pub fn certified(&self) -> Result<Vec<MoveOf<S::M>>, Violation> {
        let n = self.observed.len();
        let fail = |reason: String| Violation { index: n, now: self.now, event: "certificate".into(), reason, profile: Vec::new() };
        if !self.recording {
            return Err(fail("a certificate needs Config::certify from the start".into()));
        }
        let moves = self.certificate().map_err(fail)?;
        match certificate::certify(self.engine.model(), self.init.clone(), moves.iter().cloned()) {
            Ok(shown) if shown == self.observed => Ok(moves),
            Ok(_) => Err(fail("the certificate shows a different history".into())),
            Err(k) => Err(fail(format!("certify rejects move {k}: {:?}", moves[k]))),
        }
    }

    /// The moves of one candidate: what it recorded, with work and dispatches
    /// named by position and each read-only call placed where it took effect.
    fn certificate(&self) -> Result<Vec<MoveOf<S::M>>, String> {
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
                Record::Commit { call, res } => {
                    chosen.insert(pick(call, &|r| r == res).ok_or(format!("call {call}: no early answer {res:?}"))?);
                    placed.insert(*call);
                }
                Record::Obs(Event::Return { call, res, .. }) if !placed.contains(call) => {
                    chosen.insert(pick(call, &|r| model.admits(r, res)).ok_or(format!("call {call}: no early answer admits {res:?}"))?);
                }
                _ => {}
            }
        }
        let mut c = certificate::Config::initial(model, self.init.clone());
        let mut moves = Vec::new();
        for (k, r) in recs.into_iter().enumerate() {
            let mv = match r {
                Record::Obs(Event::Invoke { call, req, .. }) => Move::Invoke { call, req },
                Record::Obs(Event::Return { call, res, .. }) => Move::Return { call, res },
                Record::Obs(Event::Receive { msg, .. }) => {
                    Move::Receive { i: c.sent.iter().position(|m| *m == msg).ok_or(format!("{msg:?} was not sent"))? }
                }
                Record::Effect { call, j } => Move::Effect { call, j },
                Record::Early { call, j, .. } if chosen.contains(&k) => Move::Effect { call, j },
                Record::Early { .. } | Record::Commit { .. } => continue,
                Record::Run { work, j } => {
                    Move::Run { i: c.work.iter().position(|w| *w == work).ok_or(format!("{work:?} is not pending"))?, j }
                }
                Record::Advance(to) => Move::Advance { to },
            };
            c.apply(mv.clone()).map_err(|()| format!("move {} is not legal: {mv:?}", moves.len()))?;
            moves.push(mv);
        }
        Ok(moves)
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
            (Ev::Invoke(call, req), true) => Some(Event::Invoke { at: self.now, call: *call, req: req.clone() }),
            (Ev::Return(call, res), true) => Some(Event::Return { at: self.now, call: *call, res: res.clone() }),
            (Ev::Receive(msg), true) => Some(Event::Receive { at: self.now, msg: msg.clone() }),
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
            Ev::Tick(to) => {
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
            Ev::Quiesce => {
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
                let m = Node { state, pending, trail: n.trail.clone() };
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
                // Created at the first event: the clock may have moved since 0.
                let trail = match self.now {
                    0 => Trail::default(),
                    now => self.record(&Trail::default(), || Record::Advance(now)),
                };
                let node = Node { state: self.states.intern(rest), pending: HashedSet::new(), trail };
                ((0..self.factors.len()).collect(), Factor { parts: None, nodes: vec![node] })
            }
            Scope::Parts(parts) => {
                let hit: Vec<usize> = (0..self.factors.len())
                    .filter(|&i| self.factors[i].parts.as_ref().is_some_and(|ps| !ps.is_disjoint(&parts)))
                    .collect();
                let claimed: BTreeSet<S::Part> = hit.iter().flat_map(|&i| self.factors[i].parts.iter().flatten().cloned()).collect();
                let new: BTreeSet<S::Part> = parts.difference(&claimed).cloned().collect();
                let state = self.engine.restrict(&self.init, &|p| new.contains(p));
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
        let Ev::Tick(to) = *e else {
            return self.instant(index, e);
        };
        let saved = (self.profile.clone(), self.now);
        // One stop at a time: work that fires at a stop can set a deadline
        // before the next one.
        while self.now < to {
            let t = self.next_instant(to);
            if let Err(v) = self.instant(index, &Ev::Tick(t)) {
                (self.profile, self.now) = saved;
                return Err(v);
            }
        }
        Ok(())
    }

    /// The first instant in `(now, to]` at which some candidate's work becomes
    /// due or its deadline passes, or `to`.
    fn next_instant(&self, to: Time) -> Time {
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
        ts.into_iter().find(|t| *t > self.now).unwrap_or(to)
    }

    fn instant(&mut self, index: usize, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Result<(), Violation> {
        let mut explored = 0usize;
        let mut next = Vec::new();
        let mut seen = HashSet::new();
        for n in &self.profile {
            for p in self.prepare(n, e) {
                let found = match e {
                    Ev::Tick(t) => self.before_tick(p, *t, &mut explored),
                    _ => self.explain(p, e, &mut explored),
                }
                .map_err(|reason| self.violation(index, e, reason))?;
                next.extend(found.into_iter().filter(|m| seen.insert(m.clone())));
            }
        }
        if let Ev::Tick(t) = *e {
            // The clock moves; whatever is now overdue fires at the new instant, first.
            let old = std::mem::replace(&mut self.now, t);
            let mut after = Vec::new();
            let mut seen = HashSet::new();
            for n in next {
                let n = Node { trail: self.record(&n.trail, || Record::Advance(t)), ..n };
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

    fn violation(&self, index: usize, e: &Ev<Ex<S>, Re<S>, Ms<S>>, reason: String) -> Violation {
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
    fn prepare(&self, n: &Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Vec<Node<S>> {
        let (Ev::Tick(t), Some(life)) = (e, self.cfg.request_lifetime) else {
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
            out.push(Node { state: n.state.clone(), pending, trail: n.trail.clone() });
        }
        out
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
        let relevant = if matches!(e, Ev::Quiesce) || !self.cfg.footprints {
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
            if !self.owed(m, e).is_empty() || unsent(m) {
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
        let relevant = if self.cfg.footprints { self.relevant(&n, &forced, Touches::Only(Vec::new())) } else { Touches::Everything };
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
    fn owed<'a>(&self, m: &'a Node<S>, e: &Ev<Ex<S>, Re<S>, Ms<S>>) -> Vec<&'a P<S>> {
        let returning = match e {
            Ev::Return(c, r) => Some((*c, Some(r))),
            _ => None,
        };
        self.owed_for(m, returning, matches!(e, Ev::Quiesce))
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
    fn relevant(&self, n: &Node<S>, owed: &[&P<S>], seed: Touches<S::Key>) -> Touches<S::Key> {
        let mut keys: BTreeSet<S::Key> = match seed {
            Touches::Everything => return Touches::Everything,
            Touches::Only(ks) => ks.into_iter().collect(),
        };
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
            Pending::Responded { .. } | Pending::Sent { .. } => false,
        }
    }

    fn keys(&self, item: &P<S>) -> Touches<S::Key> {
        match item {
            Pending::InFlight { op, .. } => self.engine.external_keys(op),
            Pending::Step { step, .. } => self.engine.internal_keys(step),
            Pending::Responded { .. } => Touches::Only(Vec::new()),
            Pending::Sent { msg, .. } => self.engine.dispatch_keys(msg),
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
                let read_only = outs.iter().all(|o| o.spawn.is_empty() && o.send.is_empty() && o.next == *m.state);
                if !read_only {
                    return outs
                        .into_iter()
                        .enumerate()
                        .map(|(j, o)| {
                            let mut p = without();
                            p.insert(Pending::Responded { call: *call, resp: o.res });
                            self.spawn(&mut p, o.spawn);
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
                    if !seen.contains(&o.res) {
                        trail = self.record(&trail, || Record::Early { call: *call, j, res: o.res.clone() });
                        seen.insert(o.res);
                    }
                }
                if *must {
                    return seen
                        .into_iter()
                        .map(|resp| {
                            let mut p = without();
                            let trail = self.record(&trail, || Record::Commit { call: *call, res: resp.clone() });
                            p.insert(Pending::Responded { call: *call, resp });
                            Node { state: m.state.clone(), pending: p, trail }
                        })
                        .collect();
                }
                let mut p = without();
                p.insert(Pending::InFlight { call: *call, op: op.clone(), since: *since, must: false, early: seen });
                vec![Node { state: m.state.clone(), pending: p, trail }]
            }
            Pending::Step { step, after, by, must } if *after <= self.now => {
                self.engine
                    .model()
                    .internal(step, &m.state, self.now)
                    .into_iter()
                    .enumerate()
                    .map(|(j, s)| {
                        let mut p = without();
                        self.spawn(&mut p, s.spawn);
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

    fn spawn(&self, pending: &mut HashedSet<P<S>>, steps: Vec<Sched<In<S>>>) {
        for sched in steps {
            let now = self.now;
            let (step, item) = match sched {
                Sched::Later(step) => (step.clone(), Pending::Step { step, after: now, by: None, must: true }),
                Sched::Timer(at, step) => {
                    let at = at.max(now);
                    (step.clone(), Pending::Step { step, after: at, by: Some(at), must: true })
                }
                Sched::After(at, step) => (step.clone(), Pending::Step { step, after: at.max(now), by: None, must: true }),
                Sched::Within(d, step) => (step.clone(), Pending::Step { step, after: now, by: Some(now + d), must: true }),
                Sched::Maybe(step) => (step.clone(), Pending::Step { step, after: now, by: None, must: false }),
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
            pending.insert(item);
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
                p.insert(Pending::InFlight { call: *call, op: op.clone(), since: self.now, must: false, early: BTreeSet::new() });
            }
            Ev::Return(call, observed) => {
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
                            let at = self.now;
                            let trail = self.record(&m.trail, || Record::Obs(Event::Receive { at, msg: msg.clone() }));
                            Some(Node { state: m.state.clone(), pending: q, trail })
                        }
                        _ => None,
                    })
                    .collect());
            }
            Ev::Tick(_) | Ev::Quiesce => {}
        }
        let at = self.now;
        let trail = match e {
            Ev::Invoke(call, req) => self.record(&m.trail, || Record::Obs(Event::Invoke { at, call: *call, req: req.clone() })),
            Ev::Return(call, res) => self.record(&m.trail, || Record::Obs(Event::Return { at, call: *call, res: res.clone() })),
            _ => m.trail.clone(),
        };
        Ok(vec![Node { state: m.state.clone(), pending: p, trail }])
    }

    fn record(&self, trail: &Tr<S>, rec: impl FnOnce() -> Rec<S>) -> Tr<S> {
        if self.recording {
            trail.push(rec())
        } else {
            trail.clone()
        }
    }
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

/// Work a node may simply never do, and messages it may never deliver: dropping
/// them cannot add behaviors.
fn optional<O, R, T, G>(item: &Pending<O, R, T, G>) -> bool {
    matches!(item, Pending::Step { must: false, .. } | Pending::Sent { .. })
}

/// An item with its early answers cleared, so calls compare by identity alone.
fn skeleton<O: Clone, R: Clone, T: Clone, G: Clone>(item: &Pending<O, R, T, G>) -> Pending<O, R, T, G> {
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
