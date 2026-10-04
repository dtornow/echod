//! Executable behavioral specifications, after Microsoft Accordant.
//!
//! A [`Spec`] says, for any state and any request, which responses are allowed and
//! how the state changes. A [`Checker`] replays an observed history against it and
//! keeps the *profile*: every (state, pending work) pair that is still consistent
//! with what has been seen.
//!
//! Three things differ from Accordant:
//!
//! * **Request and response are separate events.** A call is `Invoke`, then a
//!   linearization point the checker places, then `Return` (or `Lost`). Coupled
//!   calls are `Invoke` immediately followed by `Return`.
//! * **Background work is data, not closures.** A [`Spec::Step`] is a value, so two
//!   branches that spawn the same step converge on the same node.
//! * **"Eventually" has a budget.** An obligation may lag at most `within`
//!   responses before it must fire; a lost request may still take effect for at
//!   most `ghost_ttl` responses. Bounded lag is what keeps the profile small.

mod checker;
mod hashed_map;
mod intern;

pub use checker::{Checker, Config, Event, Node, Pending, Stats, Violation};
pub use hashed_map::HashedMap;
pub use intern::{Interned, Interner};

use std::fmt::Debug;
use std::hash::Hash;

/// Values the checker stores in nodes: cloned, hashed, and kept in sorted sets.
pub trait Data: Clone + Eq + Hash + Ord + Debug {}
impl<T: Clone + Eq + Hash + Ord + Debug> Data for T {}

pub type CallId = u64;

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

/// How a step must behave over time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fairness {
    /// May fire, may never fire (a daemon, a retry that is allowed but not owed).
    May,
    /// Must fire. `within: Some(k)`: it has fired by the time the `k`-th later
    /// response completes (a call that linearized just before may still miss it),
    /// and once overdue it fires before every response while it is enabled. `None` defers the
    /// obligation to the next [`Event::Quiesce`].
    Eventually { within: Option<u32> },
}

/// One possible effect of a request at its linearization point.
pub struct Outcome<S: Spec + ?Sized> {
    pub resp: S::Resp,
    pub next: S::State,
    pub spawn: Vec<S::Step>,
}

impl<S: Spec + ?Sized> Outcome<S> {
    pub fn new(resp: S::Resp, next: S::State) -> Self {
        Outcome { resp, next, spawn: Vec::new() }
    }

    /// The response, with the state unchanged.
    pub fn same(resp: S::Resp, state: &S::State) -> Self {
        Outcome::new(resp, state.clone())
    }

    /// Background work this outcome starts.
    pub fn spawn(mut self, step: S::Step) -> Self {
        self.spawn.push(step);
        self
    }
}

/// Result of trying a background step in a state.
pub enum StepResult<S: Spec + ?Sized> {
    /// Not enabled here; stays pending.
    Disabled,
    /// Its work is done (Accordant's `IsTerminalState`); removed without a state change.
    Discharged,
    /// Fires: each entry is one non-deterministic successor and the steps it spawns.
    Next(Vec<(S::State, Vec<S::Step>)>),
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

    /// The linearization point of `op` in `state`: every allowed outcome.
    /// An empty list means `op` cannot take effect in this state.
    fn apply(&self, op: &Self::Op, state: &Self::State) -> Vec<Outcome<Self>>;

    fn step(&self, _step: &Self::Step, _state: &Self::State) -> StepResult<Self> {
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
}
