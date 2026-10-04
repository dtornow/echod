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
//! * **When internal work runs is part of starting it** ([`Sched`]): later,
//!   at a timer, after a time, within a window, or maybe never. Deadlines are
//!   what keep the search small.
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
    /// What the system sends to clients on its own, from internal work (an
    /// "execute this task" to a worker). `()` if it sends nothing.
    type Dispatch: Data;

    /// A request takes effect in `state` at `now`: every allowed outcome. An
    /// empty list means it cannot take effect here.
    fn external(&self, req: &Self::External, state: &Self::State, now: Time) -> Vec<ExternalOutcome<Self>>;

    /// Internal work runs in `state` at `now`: every possible successor. An empty
    /// list means it can't run yet and stays pending; `InternalOutcome::same(state)` means it
    /// has nothing left to do and is removed.
    fn internal(&self, _req: &Self::Internal, _state: &Self::State, _now: Time) -> Vec<InternalOutcome<Self>> {
        Vec::new()
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

    /// The keys a server-sent message is about: receiving it can only be
    /// explained by internal work on these keys.
    fn dispatch_touches(&self, _msg: &Self::Dispatch) -> Touches<Self::Key> {
        Touches::Everything
    }
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

/// Internal work to start, and when it runs. Work that must happen and hasn't
/// by its deadline is a violation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sched<T> {
    /// Runs later: any time from now on; must have happened by the next `Quiesce`.
    Later(T),
    /// A timer: runs exactly at the given time.
    Timer(Time, T),
    /// Runs any time after the given time; must have happened by the next `Quiesce`.
    After(Time, T),
    /// Runs any time from now on; must have happened within the given duration.
    Within(Time, T),
    /// May run any time from now on, or never.
    Maybe(T),
}

/// One possible effect of a request: the next state, the response, and the
/// internal work it starts.
pub struct ExternalOutcome<M: Model + ?Sized> {
    pub next: M::State,
    pub resp: M::Response,
    pub spawn: Vec<Sched<M::Internal>>,
}

impl<M: Model + ?Sized> ExternalOutcome<M> {
    pub fn new(resp: M::Response, next: M::State) -> Self {
        ExternalOutcome { next, resp, spawn: Vec::new() }
    }

    /// The response, with the state unchanged.
    pub fn same(resp: M::Response, state: &M::State) -> Self {
        ExternalOutcome::new(resp, state.clone())
    }

    /// Internal work that runs later.
    pub fn later(mut self, step: M::Internal) -> Self {
        self.spawn.push(Sched::Later(step));
        self
    }

    /// Internal work that runs exactly at `at`.
    pub fn timer(mut self, at: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched::Timer(at, step));
        self
    }

    /// Internal work that runs any time after `at`, eventually.
    pub fn after(mut self, at: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched::After(at, step));
        self
    }

    /// Internal work that runs within `d` from now.
    pub fn within(mut self, d: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched::Within(d, step));
        self
    }

    /// Internal work that may run, or never.
    pub fn maybe(mut self, step: M::Internal) -> Self {
        self.spawn.push(Sched::Maybe(step));
        self
    }
}

/// One possible effect of internal work: the next state, the internal work it
/// starts, and the messages it sends to clients (server-sent, observed with
/// [`Checker::receive`]).
pub struct InternalOutcome<M: Model + ?Sized> {
    pub next: M::State,
    pub spawn: Vec<Sched<M::Internal>>,
    pub send: Vec<M::Dispatch>,
}

impl<M: Model + ?Sized> InternalOutcome<M> {
    pub fn new(next: M::State) -> Self {
        InternalOutcome { next, spawn: Vec::new(), send: Vec::new() }
    }

    /// A message to a client. It may be received once, at any time after, or never.
    pub fn send(mut self, msg: M::Dispatch) -> Self {
        self.send.push(msg);
        self
    }

    /// Runs and changes nothing: the work is done.
    pub fn same(state: &M::State) -> Self {
        InternalOutcome::new(state.clone())
    }

    /// Internal work that runs later.
    pub fn later(mut self, step: M::Internal) -> Self {
        self.spawn.push(Sched::Later(step));
        self
    }

    /// Internal work that runs exactly at `at`.
    pub fn timer(mut self, at: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched::Timer(at, step));
        self
    }

    /// Internal work that runs any time after `at`, eventually.
    pub fn after(mut self, at: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched::After(at, step));
        self
    }

    /// Internal work that runs within `d` from now.
    pub fn within(mut self, d: Time, step: M::Internal) -> Self {
        self.spawn.push(Sched::Within(d, step));
        self
    }

    /// Internal work that may run, or never.
    pub fn maybe(mut self, step: M::Internal) -> Self {
        self.spawn.push(Sched::Maybe(step));
        self
    }
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

    fn dispatch_keys(&self, _msg: &<Self::M as Model>::Dispatch) -> Touches<Self::Key> {
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

    fn dispatch_keys(&self, msg: &M::Dispatch) -> Touches<M::Key> {
        self.0.dispatch_touches(msg)
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

    fn dispatch_keys(&self, msg: &M::Dispatch) -> Touches<M::Key> {
        self.0.dispatch_touches(msg)
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
