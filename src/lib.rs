//! Executable behavioral specifications, after Microsoft Accordant.
//!
//! A [`Spec`] says, for any state, time and request, which responses are allowed
//! and how the state changes. A [`Checker`] replays an observed history against it
//! and keeps the *profile*: every (state, pending work) pair that is still
//! consistent with what has been seen.
//!
//! Four things differ from Accordant:
//!
//! * **Request and response are separate events.** A call is `Invoke`, then a
//!   linearization point the checker places, then `Return`. A call that never
//!   returns stays in flight: it may or may not have taken effect, because the
//!   client cannot know. Coupled calls are `Invoke` immediately followed by `Return`.
//! * **Time is first class.** The checker owns the clock; `tick` advances it. Specs
//!   read `now`, install timers, and give obligations deadlines in time.
//! * **Background work is data, not closures.** A [`Spec::Step`] is a value, so two
//!   branches that spawn the same step converge on the same node.
//! * **"Eventually" has a deadline.** An obligation must fire within its window;
//!   an unanswered request takes effect within `request_lifetime` or never.
//!   Bounded windows are what keep the profile small.

mod checker;
mod hashed_map;
mod intern;

pub use checker::{Checker, Config, Event, Factor, Node, Pending, Stats, Violation};
pub use hashed_map::HashedMap;
pub use intern::{Interned, Interner};

use std::fmt::Debug;
use std::hash::Hash;

/// Values the checker stores in nodes: cloned, hashed, and kept in sorted sets.
pub trait Data: Clone + Eq + Hash + Ord + Debug {}
impl<T: Clone + Eq + Hash + Ord + Debug> Data for T {}

pub type CallId = u64;

/// Logical time, in whatever unit the spec uses (milliseconds in the examples).
pub type Time = u64;

/// What a request or step may read or write. Work whose keys are disjoint from
/// what an observation depends on commutes with it and is not explored.
#[derive(Clone, Debug)]
pub enum Keys<K> {
    All,
    Some(Vec<K>),
}

impl<K> Keys<K> {
    pub fn one(k: K) -> Self {
        Keys::Some(vec![k])
    }
}

/// How a step must behave over time, measured from when it becomes due (its timer
/// time, or the moment it was spawned).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fairness {
    /// May fire, may never fire (a daemon, a retry that is allowed but not owed).
    May,
    /// Must fire. `within: Some(d)`: by `due + d`; `Some(0)` is an exact timer.
    /// Once overdue it fires as soon as it is enabled. `None` defers the
    /// obligation to the next [`Event::Quiesce`].
    Eventually { within: Option<Time> },
}

/// A step to start: now, or as a timer at an absolute time.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sched<T> {
    pub step: T,
    pub at: Option<Time>,
}

/// One possible effect of a request at its linearization point.
pub struct Outcome<S: Spec + ?Sized> {
    pub resp: S::Resp,
    pub next: S::State,
    pub spawn: Vec<Sched<S::Step>>,
}

impl<S: Spec + ?Sized> Outcome<S> {
    pub fn new(resp: S::Resp, next: S::State) -> Self {
        Outcome { resp, next, spawn: Vec::new() }
    }

    /// The response, with the state unchanged.
    pub fn same(resp: S::Resp, state: &S::State) -> Self {
        Outcome::new(resp, state.clone())
    }

    /// Background work this outcome starts now.
    pub fn spawn(mut self, step: S::Step) -> Self {
        self.spawn.push(Sched { step, at: None });
        self
    }

    /// Background work that becomes due at `at`.
    pub fn timer(mut self, at: Time, step: S::Step) -> Self {
        self.spawn.push(Sched { step, at: Some(at) });
        self
    }
}

/// One successor of a background step.
pub struct Succ<S: Spec + ?Sized> {
    pub next: S::State,
    pub spawn: Vec<Sched<S::Step>>,
}

impl<S: Spec + ?Sized> Succ<S> {
    pub fn new(next: S::State) -> Self {
        Succ { next, spawn: Vec::new() }
    }

    pub fn spawn(mut self, step: S::Step) -> Self {
        self.spawn.push(Sched { step, at: None });
        self
    }

    pub fn timer(mut self, at: Time, step: S::Step) -> Self {
        self.spawn.push(Sched { step, at: Some(at) });
        self
    }
}

/// Result of trying a background step in a state.
pub enum StepResult<S: Spec + ?Sized> {
    /// Not enabled here; stays pending.
    Disabled,
    /// Its work is done (Accordant's `IsTerminalState`); removed without a state change.
    Discharged,
    /// Fires: each entry is one non-deterministic successor.
    Next(Vec<Succ<S>>),
}

pub trait Spec {
    type State: Clone + Eq + Hash + Debug;
    /// A request. Usually an enum with one variant per operation.
    type Op: Data;
    /// The abstract response the spec predicts; observations are mapped into it.
    type Resp: Data;
    /// A unit of background work, as a value.
    type Step: Data;
    type Key: Data;

    /// The linearization point of `op` in `state` at time `now`: every allowed
    /// outcome. An empty list means `op` cannot take effect here.
    fn apply(&self, op: &Self::Op, state: &Self::State, now: Time) -> Vec<Outcome<Self>>;

    fn step(&self, _step: &Self::Step, _state: &Self::State, _now: Time) -> StepResult<Self> {
        StepResult::Disabled
    }

    fn fairness(&self, _step: &Self::Step) -> Fairness {
        Fairness::Eventually { within: None }
    }

    /// Whether an observed response matches the predicted one. Override for
    /// wildcards (server-chosen ids, timestamps).
    fn admits(&self, expected: &Self::Resp, observed: &Self::Resp) -> bool {
        expected == observed
    }

    /// Footprints. The default, `All`, is always sound and never prunes.
    fn op_keys(&self, _op: &Self::Op) -> Keys<Self::Key> {
        Keys::All
    }

    fn step_keys(&self, _step: &Self::Step) -> Keys<Self::Key> {
        Keys::All
    }

    /// Partitioning. A partitioned spec's state splits into independent parts, and
    /// the checker keeps each part's candidates separately instead of their
    /// product. `part` names a key's partition (Resonate: the id's origin);
    /// `None`, the default, means the spec is not partitioned.
    ///
    /// Work spawned by a request or step must stay within the partitions of its
    /// own footprint.
    fn part(&self, _key: &Self::Key) -> Option<Self::Key> {
        None
    }

    /// The part of `state` belonging to the partitions `keep` accepts. Required
    /// when `part` returns `Some`.
    fn restrict(&self, _state: &Self::State, _keep: &dyn Fn(&Self::Key) -> bool) -> Self::State {
        unimplemented!("a partitioned spec must implement restrict")
    }

    /// The union of two states over disjoint partitions. Required when `part`
    /// returns `Some`.
    fn join(&self, _a: &Self::State, _b: &Self::State) -> Self::State {
        unimplemented!("a partitioned spec must implement join")
    }
}
