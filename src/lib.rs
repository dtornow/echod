//! Executable behavioral specifications, after Microsoft Accordant.
//!
//! A [`Model`] says, for any state and time, what the system does: how it answers
//! an **external** request from a client, and what **internal** work it does on
//! its own (a timeout fires, a lease expires, a resume runs). A [`Checker`]
//! replays an observed history against it and keeps every explanation of that
//! history that is still possible.
//!
//! What differs from Accordant:
//!
//! * **Request and response are separate events.** A call is `Invoke`, then a
//!   point where it takes effect that the checker places, then `Return`. A call
//!   that never returns stays in flight: it may or may not have taken effect,
//!   because the client cannot know.
//! * **Time is first class.** The checker owns the clock; `tick` advances it.
//!   Models read `now`, install timers, and give internal work deadlines.
//! * **Internal work is data, not closures,** so two explanations that start the
//!   same work converge.
//! * **"Eventually" has a deadline,** which is what keeps the search small.
//!
//! A model is checked as it is. Two optional traits make checking faster:
//! [`Footprint`] says which keys a step touches, and [`Partitioned`] groups
//! keys into independent parts. Pick the constructor that matches:
//! [`Checker::new`], [`Checker::with_footprints`] or [`Checker::with_partitions`].

mod checker;
mod hashed_map;
mod hashed_set;
mod intern;

pub use checker::{Checker, Config, Event, Factor, Node, Pending, Stats, Violation};
pub use hashed_map::HashedMap;
pub use hashed_set::HashedSet;
pub use intern::{Interned, Interner};

use std::fmt::Debug;
use std::hash::Hash;

/// Values the checker stores and compares: cloned, hashed, and kept in sorted sets.
pub trait Data: Clone + Eq + Hash + Ord + Debug {}
impl<T: Clone + Eq + Hash + Ord + Debug> Data for T {}

pub type CallId = u64;

/// Logical time, in whatever unit the model uses (milliseconds in the examples).
pub type Time = u64;

/// The system, as a state machine: external requests from clients, internal
/// work it does on its own.
pub trait Model {
    type State: Clone + Eq + Hash + Debug;
    /// External: a request a client sends.
    type External: Data;
    /// What the system answers to a request.
    type Response: Data;
    /// Internal: work the system does on its own (a timeout, a resume).
    type Internal: Data;

    /// A request takes effect in `state` at `now`: every allowed outcome. An
    /// empty list means it cannot take effect here.
    fn external(&self, req: &Self::External, state: &Self::State, now: Time) -> Vec<Outcome<Self>>;

    /// Internal work runs in `state` at `now`.
    fn internal(&self, _step: &Self::Internal, _state: &Self::State, _now: Time) -> StepResult<Self> {
        StepResult::Disabled
    }

    /// How internal work must behave over time.
    fn fairness(&self, _step: &Self::Internal) -> Fairness {
        Fairness::Eventually { within: None }
    }

    /// Whether an observed response matches the one the model predicts.
    /// Override for wildcards (server-chosen ids, timestamps).
    fn admits(&self, expected: &Self::Response, observed: &Self::Response) -> bool {
        expected == observed
    }
}

/// Optional, for speed: which keys a request or internal step touches. To
/// explain a response, the checker then only considers work on the same keys.
/// A footprint must include everything the step reads or writes.
pub trait Footprint: Model {
    /// The key of a thing in the state that steps touch: a promise id, an account name.
    type Key: Data;

    fn external_touches(&self, req: &Self::External) -> Touches<Self::Key>;

    fn internal_touches(&self, step: &Self::Internal) -> Touches<Self::Key>;
}

/// Optional, for speed: keys fall into independent groups (Resonate: by
/// origin), and the checker keeps each group's explanations apart instead of
/// their product. Internal work started by a step must stay within the groups
/// that step touches.
pub trait Partitioned: Footprint {
    type Group: Data;

    fn group(&self, key: &Self::Key) -> Self::Group;

    /// The part of `state` whose keys belong to groups `keep` accepts.
    fn restrict(&self, state: &Self::State, keep: &dyn Fn(&Self::Group) -> bool) -> Self::State;

    /// The union of two states over disjoint groups.
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State;
}

/// How internal work must behave over time, measured from when it becomes due
/// (its timer time, or the moment it was started).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fairness {
    /// May happen, may never happen (a daemon, a retry that is allowed but not owed).
    May,
    /// Must happen. `within: Some(d)`: by `due + d`; `Some(0)` is an exact timer.
    /// Once overdue it happens as soon as it can. `None` defers the obligation
    /// to the next [`Event::Quiesce`].
    Eventually { within: Option<Time> },
}

/// Internal work to start: now, or as a timer at an absolute time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sched<T> {
    pub step: T,
    pub at: Option<Time>,
}

/// One possible effect of a request: the response, the next state, and the
/// internal work it starts.
pub struct Outcome<M: Model + ?Sized> {
    pub resp: M::Response,
    pub next: M::State,
    pub spawn: Vec<Sched<M::Internal>>,
}

impl<M: Model + ?Sized> Outcome<M> {
    pub fn new(resp: M::Response, next: M::State) -> Self {
        Outcome { resp, next, spawn: Vec::new() }
    }

    /// The response, with the state unchanged.
    pub fn same(resp: M::Response, state: &M::State) -> Self {
        Outcome::new(resp, state.clone())
    }

    /// Internal work this outcome starts now.
    pub fn spawn(mut self, step: M::Internal) -> Self {
        self.spawn.push(Sched { step, at: None });
        self
    }

    /// Internal work that becomes due at `at`.
    pub fn timer(mut self, at: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched { step, at: Some(at) });
        self
    }
}

/// One possible effect of internal work.
pub struct Succ<M: Model + ?Sized> {
    pub next: M::State,
    pub spawn: Vec<Sched<M::Internal>>,
}

impl<M: Model + ?Sized> Succ<M> {
    pub fn new(next: M::State) -> Self {
        Succ { next, spawn: Vec::new() }
    }

    pub fn spawn(mut self, step: M::Internal) -> Self {
        self.spawn.push(Sched { step, at: None });
        self
    }

    pub fn timer(mut self, at: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched { step, at: Some(at) });
        self
    }
}

/// What internal work does in a state.
pub enum StepResult<M: Model + ?Sized> {
    /// Can't run here; stays pending.
    Disabled,
    /// Already done (Accordant's `IsTerminalState`); removed without a state change.
    Discharged,
    /// Runs: each entry is one possible successor.
    Next(Vec<Succ<M>>),
}

/// The keys a step touches.
#[derive(Clone, Debug)]
pub enum Touches<K> {
    /// Anything: the step may read or write any object.
    Everything,
    Only(Vec<K>),
}

impl<K> Touches<K> {
    pub fn one(k: K) -> Self {
        Touches::Only(vec![k])
    }
}

/// How the checker sees a model: the [`Model`] plus whatever of [`Footprint`]
/// and [`Partitioned`] it provides. Implemented by [`Plain`], [`Keyed`] and
/// [`Grouped`]; the [`Checker`] constructors pick one.
pub trait Engine {
    type M: Model;
    type Key: Data;
    type Part: Data;

    fn model(&self) -> &Self::M;

    fn external_keys(&self, _req: &<Self::M as Model>::External) -> Touches<Self::Key> {
        Touches::Everything
    }

    fn internal_keys(&self, _step: &<Self::M as Model>::Internal) -> Touches<Self::Key> {
        Touches::Everything
    }

    fn part(&self, _key: &Self::Key) -> Option<Self::Part> {
        None
    }

    fn restrict(
        &self,
        _state: &<Self::M as Model>::State,
        _keep: &dyn Fn(&Self::Part) -> bool,
    ) -> <Self::M as Model>::State {
        unreachable!("only a partitioned engine restricts")
    }

    fn join(&self, _a: &<Self::M as Model>::State, _b: &<Self::M as Model>::State) -> <Self::M as Model>::State {
        unreachable!("only a partitioned engine joins")
    }
}

/// A model checked as it is: every step may touch everything.
pub struct Plain<M>(pub M);

impl<M: Model> Engine for Plain<M> {
    type M = M;
    type Key = ();
    type Part = ();

    fn model(&self) -> &M {
        &self.0
    }
}

/// A model checked with its footprints.
pub struct Keyed<M>(pub M);

impl<M: Footprint> Engine for Keyed<M> {
    type M = M;
    type Key = M::Key;
    type Part = ();

    fn model(&self) -> &M {
        &self.0
    }

    fn external_keys(&self, req: &M::External) -> Touches<M::Key> {
        self.0.external_touches(req)
    }

    fn internal_keys(&self, step: &M::Internal) -> Touches<M::Key> {
        self.0.internal_touches(step)
    }
}

/// A model checked with its footprints and partitions.
pub struct Grouped<M>(pub M);

impl<M: Partitioned> Engine for Grouped<M> {
    type M = M;
    type Key = M::Key;
    type Part = M::Group;

    fn model(&self) -> &M {
        &self.0
    }

    fn external_keys(&self, req: &M::External) -> Touches<M::Key> {
        self.0.external_touches(req)
    }

    fn internal_keys(&self, step: &M::Internal) -> Touches<M::Key> {
        self.0.internal_touches(step)
    }

    fn part(&self, key: &M::Key) -> Option<M::Group> {
        Some(self.0.group(key))
    }

    fn restrict(&self, state: &M::State, keep: &dyn Fn(&M::Group) -> bool) -> M::State {
        self.0.restrict(state, keep)
    }

    fn join(&self, a: &M::State, b: &M::State) -> M::State {
        self.0.join(a, b)
    }
}
