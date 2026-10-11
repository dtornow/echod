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
//! * **Time is the system's clock, recorded in the trace.** Observations carry
//!   no timestamps; their order is the real-time order, as one observer saw it.
//!   When the system's clock moves, the trace says so ([`Event::Clock`]). The
//!   model reads the clock (`now` is an argument of [`Model::external`] and
//!   [`Model::internal`]) and never moves it. Models install timers and give
//!   internal work deadlines on that clock, and the checker enforces them.
//! * **Internal work is data, not closures,** so two explanations that start the
//!   same work converge.
//! * **When internal work runs is part of starting it** ([`Sched`]): later
//!   or at a timer. Deadlines are what keep the search small.
//!
//! A model is checked as it is. Two optional traits make checking faster:
//! [`Footprint`] says which keys a step touches, and [`Partitioned`] groups
//! keys into independent parts. Pick the constructor that matches:
//! [`Checker::new`], [`Checker::with_footprints`] or [`Checker::with_partitions`].

mod certificate;
mod checker;
mod drive;
mod sim;
mod hashed_map;
mod hashed_set;
mod intern;
pub mod semantics;

pub use certificate::{certify, marks, Certificate, Silent};
pub use drive::{drive, Choice, Choices, Drive, Run, Tried};
pub use sim::Sim;
pub use checker::{Checker, Config, Factor, Node, Pending, Stats, Verdict, Violation};
pub use hashed_map::HashedMap;
pub use hashed_set::HashedSet;
pub use intern::{Interned, Interner};

use std::fmt::Debug;
use std::hash::Hash;

use vstd::prelude::*;

// What the proofs talk about is written in Verus: the model's interface and
// what a client observes. `cargo build` compiles it as ordinary Rust, the
// specifications erased; `cargo verus verify -p accordant` checks the proofs
// (`semantics`, `certificate`).
verus! {

/// Values the checker stores and compares: cloned, hashed, and kept in sorted sets.
pub trait Data: Clone + Eq + Hash + Ord + Debug {}
impl<T: Clone + Eq + Hash + Ord + Debug> Data for T {}

pub type CallId = u64;

/// The system's clock, in whatever unit it uses (milliseconds in the examples).
/// It is part of the configuration the checker keeps, moved only by
/// [`Event::Clock`]; the model reads it and never moves it.
pub type Time = u64;

/// What a client observes, and when the system's clock moved. Observations
/// carry no timestamps: the order of a trace is the order one observer saw.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Event<X, R, D> {
    /// The client sent a request.
    Invoke { call: CallId, req: X },
    /// The client got the response to that call.
    Return { call: CallId, res: R },
    /// The client got a dispatch the server sent on its own.
    Receive { msg: D },
    /// The system's clock now reads `at`. Work due by then is overdue, and
    /// runs before anything else is observed.
    Clock { at: Time },
}

/// Internal work to start, and when it runs, on the system's clock as it reads
/// when the starting step is taken. Work that must happen and hasn't by its
/// deadline is a violation. When the clock jumps past several deadlines,
/// the work runs right after the jump, earliest deadline first.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Sched<T> {
    /// Runs later: any time from now on, when an observation needs it, or never.
    Later(T),
    /// A timer: runs exactly at the given time.
    Timer(Time, T),
}

/// One possible effect of a request: the next state, the response, the
/// internal work it starts, and the dispatches it sends. `marks`: names for
/// what this outcome does ("lease expired"), for coverage; they change nothing.
pub struct ExternalOutcome<M: Model + ?Sized> {
    pub next: M::State,
    pub resp: M::Response,
    pub work: Vec<Sched<M::Internal>>,
    pub send: Vec<M::Dispatch>,
    pub marks: Vec<&'static str>,
}

/// One possible effect of internal work: the next state, the internal work it
/// starts, and the messages it sends to clients (server-sent, observed with
/// [`Checker::receive`]). `marks` as for [`ExternalOutcome`].
pub struct InternalOutcome<M: Model + ?Sized> {
    pub next: M::State,
    pub work: Vec<Sched<M::Internal>>,
    pub send: Vec<M::Dispatch>,
    pub marks: Vec<&'static str>,
}

/// The system, as a state machine: external requests from clients, internal
/// work it does on its own. It reads the clock (`now`) and never moves it:
/// the trace says when time moved ([`Event::Clock`]).
///
/// Each method has a `spec` twin the proofs use ([`semantics`]), and must
/// compute what its twin says (its `ensures`). A model written outside
/// `verus!` keeps the default twins, which then stand for whatever the methods
/// compute: they must be pure, and nothing checks that. A model written in
/// Verus overrides the twins and has its methods verified against them.
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

    /// A request takes effect in `state` at time `now`: every allowed outcome.
    /// At least one: every request is accepted in every state. A system
    /// always answers; refusing is a response.
    fn external(&self, req: &Self::External, state: &Self::State, now: Time) -> (r: Vec<ExternalOutcome<Self>>)
        ensures
            r@.len() == self.spec_external(*req, *state, now).len(),
            forall|i: int| 0 <= i < r@.len() ==> {
                let o = #[trigger] r@[i];
                semantics::ExternalOutcomeV { next: o.next, resp: o.resp, work: o.work@, send: o.send@ }
                    == self.spec_external(*req, *state, now)[i]
            };

    /// Internal work runs in `state` at time `now`: every possible successor.
    /// An empty list means it can't run yet and stays pending;
    /// `InternalOutcome::same(state)` means it has nothing left to do and is
    /// removed.
    fn internal(&self, req: &Self::Internal, state: &Self::State, now: Time) -> (r: Vec<InternalOutcome<Self>>)
        ensures
            r@.len() == self.spec_internal(*req, *state, now).len(),
            forall|i: int| 0 <= i < r@.len() ==> {
                let o = #[trigger] r@[i];
                semantics::InternalOutcomeV { next: o.next, work: o.work@, send: o.send@ }
                    == self.spec_internal(*req, *state, now)[i]
            };

    /// What [`Model::external`] computes, for the proofs.
    open spec fn spec_external(&self, req: Self::External, state: Self::State, now: Time) -> Seq<
        semantics::ExternalOutcomeV<Self::State, Self::Response, Self::Internal, Self::Dispatch>,
    > {
        arbitrary()
    }

    /// What [`Model::internal`] computes, for the proofs.
    open spec fn spec_internal(&self, req: Self::Internal, state: Self::State, now: Time) -> Seq<
        semantics::InternalOutcomeV<Self::State, Self::Internal, Self::Dispatch>,
    > {
        arbitrary()
    }
}

} // verus!

/// What a driver can do to the system besides letting it run: send a request,
/// or move its clock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Action<X> {
    Request(X),
    /// The clock moves forward to this time ([`Event::Clock`]).
    Clock(Time),
}

/// Optional, for driving a model ([`drive`]): what to do to it.
pub trait Explore: Model {
    /// Actions worth trying from `state` at `now`, each with why: the ones
    /// that reach the edges of what the state allows (a request that just
    /// fits, a clock move to just past a deadline).
    fn suggest(&self, state: &Self::State, now: Time) -> Vec<(Action<Self::External>, &'static str)>;

    /// Any action, from `state` at `now`; `pick(n)` chooses among `n`
    /// alternatives (recorded, so a run can be replayed).
    fn arbitrary(&self, state: &Self::State, now: Time, pick: &mut dyn FnMut(usize) -> usize) -> Action<Self::External>;

    /// Actions to take at the end of a run, one at a time, each settled before
    /// the next (reads that show the final state, say). None by default.
    fn finish(&self, _state: &Self::State, _now: Time) -> Vec<Action<Self::External>> {
        Vec::new()
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

impl<M: Model + ?Sized> ExternalOutcome<M> {
    pub fn new(resp: M::Response, next: M::State) -> Self {
        ExternalOutcome { next, resp, work: Vec::new(), send: Vec::new(), marks: Vec::new() }
    }

    /// A name for what this outcome does, for coverage: the marks along the
    /// execution a certificate describes are what a trace exercised
    /// ([`marks`]). Changes nothing.
    pub fn mark(mut self, name: &'static str) -> Self {
        self.marks.push(name);
        self
    }

    /// The response, with the state unchanged.
    pub fn same(resp: M::Response, state: &M::State) -> Self {
        ExternalOutcome::new(resp, state.clone())
    }

    /// A dispatch to a client, sent when the request takes effect. It may be
    /// received once, at any time after, or never.
    pub fn send(mut self, msg: M::Dispatch) -> Self {
        self.send.push(msg);
        self
    }

    /// Internal work that runs later.
    pub fn later(mut self, step: M::Internal) -> Self {
        self.work.push(Sched::Later(step));
        self
    }

    /// Internal work that runs exactly at `at`.
    pub fn timer(mut self, at: Time, step: M::Internal) -> Self {
        self.work.push(Sched::Timer(at, step));
        self
    }
}

impl<M: Model + ?Sized> InternalOutcome<M> {
    pub fn new(next: M::State) -> Self {
        InternalOutcome { next, work: Vec::new(), send: Vec::new(), marks: Vec::new() }
    }

    /// A name for what this outcome does, for coverage. Changes nothing.
    pub fn mark(mut self, name: &'static str) -> Self {
        self.marks.push(name);
        self
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
        self.work.push(Sched::Later(step));
        self
    }

    /// Internal work that runs exactly at `at`.
    pub fn timer(mut self, at: Time, step: M::Internal) -> Self {
        self.work.push(Sched::Timer(at, step));
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

    /// Whether the engine keeps partitions apart.
    fn partitioned(&self) -> bool {
        false
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

    fn partitioned(&self) -> bool {
        true
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
