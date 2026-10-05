//! What the accordant checker promises, in Verus.
//!
//! In one sentence:
//!
//! > If the checker accepts a trace, then some execution of the system,
//! > projected onto what clients observe, is exactly that trace.
//!
//! In Verus, at the bottom of this file, as the contract of the Rust function:
//!
//! ```text
//! fn check(m, init, trace) -> (accepted: bool)
//!     ensures accepted ==> valid(m, init, trace)
//!
//! valid(m, init, trace) :=
//!     exists steps. legal(m, initial(m, init), steps) && project(steps) == trace
//! ```
//!
//! Everything above defines its words, as in `lean/Accordant.lean`:
//! `Event` (what a client observes), `Model` (the system), `step` (how the
//! system evolves; each step observed or silent), `legal` (steps the system can
//! actually take), `project` (what an execution shows a client).
//!
//! `check` stands for the checker with certificates,
//! `Checker::new(m, init, Config::default()).check_certified(trace).is_ok()`.
//! It is `external_body`: Verus takes the contract on trust. The proof is in
//! `lean/Accordant.lean`: a certificate that `certify` accepts is valid, so the
//! contract holds as long as `src/certificate.rs` matches the Lean `certify`.
//!
//! Not covered: `assert_idle`.

use vstd::prelude::*;

verus! {

/// Time as clients and the model see it.
pub type Time = u64;

pub type CallId = u64;

// ------------------------------------------------------------- observations

/// What a client observes. No time: a trace's order is the order one observer saw.
pub enum Event<X, R, D> {
    /// The client sent a request.
    Invoke { call: CallId, req: X },
    /// The client got the response to that call.
    Return { call: CallId, res: R },
    /// The client got a dispatch the server sent on its own.
    Receive { msg: D },
}

// -------------------------------------------------------------------- model

/// Internal work to start, and when it runs.
pub enum Sched<I> {
    /// From now on; must have happened by the time the system is idle.
    Later(I),
    /// Exactly at the given time.
    Timer(Time, I),
}

/// One possible effect of a request.
pub struct ExternalOutcome<S, R, I, D> {
    pub next: S,
    pub resp: R,
    pub work: Seq<Sched<I>>,
    pub send: Seq<D>,
}

/// One possible effect of internal work.
pub struct InternalOutcome<S, I, D> {
    pub next: S,
    pub work: Seq<Sched<I>>,
    pub send: Seq<D>,
}

/// The system, as a state machine: requests from clients, work it does on its own.
pub trait Model {
    type State;
    type External;
    type Response;
    type Internal;
    type Dispatch;

    /// A request takes effect: every allowed outcome.
    spec fn external(&self, req: Self::External, state: Self::State) -> Seq<
        ExternalOutcome<Self::State, Self::Response, Self::Internal, Self::Dispatch>,
    >;

    /// Internal work runs: every possible outcome. Empty: it can't run yet.
    spec fn internal(&self, req: Self::Internal, state: Self::State) -> Seq<
        InternalOutcome<Self::State, Self::Internal, Self::Dispatch>,
    >;

    /// Whether a client seeing `observed` matches the `expected` response.
    spec fn admits(&self, expected: Self::Response, observed: Self::Response) -> bool;

    /// The model's clock in a state. Deadlines are on this clock.
    spec fn now(&self, state: Self::State) -> Time;

    /// The work the system starts with, in the initial state.
    spec fn start(&self, state: Self::State) -> Seq<Sched<Self::Internal>>;
}

pub type Ev<M> = Event<<M as Model>::External, <M as Model>::Response, <M as Model>::Dispatch>;

// --------------------------------------------------------------------- runs

/// A call the client has sent and not yet seen answered.
pub enum Call<X, R> {
    /// Not yet taken effect.
    InFlight(X),
    /// Taken effect; the client will see this response.
    Done(R),
}

/// Internal work started and not yet run.
pub struct Work<I> {
    pub req: I,
    /// Can't run before this time.
    pub after: nat,
    /// Must have run by this time, if it can run then.
    pub by: Option<nat>,
    /// Must run at some point (false: `Maybe`).
    pub must: bool,
}

/// Everything about a run at one point, seen or not.
pub struct Config<S, X, R, I, D> {
    pub state: S,
    pub calls: Map<CallId, Call<X, R>>,
    pub work: Seq<Work<I>>,
    /// Dispatches sent and not yet received.
    pub sent: Seq<D>,
}

pub type Cfg<M> = Config<
    <M as Model>::State,
    <M as Model>::External,
    <M as Model>::Response,
    <M as Model>::Internal,
    <M as Model>::Dispatch,
>;

/// A step either shows a client an observation, or nothing.
pub enum Label<X, R, D> {
    Obs(Event<X, R, D>),
    Silent,
}

pub type Lab<M> = Label<<M as Model>::External, <M as Model>::Response, <M as Model>::Dispatch>;

pub open spec fn max(a: nat, b: nat) -> nat {
    if a >= b { a } else { b }
}

pub open spec fn schedule<I>(s: Sched<I>, now: nat) -> Work<I> {
    match s {
        Sched::Later(req) => Work { req, after: now, by: None, must: true },
        Sched::Timer(at, req) => Work { req, after: max(at as nat, now), by: Some(max(at as nat, now)), must: true },
    }
}

pub open spec fn start_all<I>(work: Seq<Work<I>>, new: Seq<Sched<I>>, now: nat) -> Seq<Work<I>> {
    work + new.map_values(|s: Sched<I>| schedule(s, now))
}

pub open spec fn clock<M: Model>(m: M, c: Cfg<M>) -> nat {
    m.now(c.state) as nat
}

/// Work whose deadline has come on the model's clock, and that can run: it runs
/// before anything else happens.
pub open spec fn is_overdue<M: Model>(m: M, c: Cfg<M>, i: int) -> bool {
    0 <= i < c.work.len() && c.work[i].must && c.work[i].after <= clock(m, c) && match c.work[i].by {
        Some(by) => by <= clock(m, c) && m.internal(c.work[i].req, c.state).len() > 0,
        None => false,
    }
}

pub open spec fn overdue<M: Model>(m: M, c: Cfg<M>) -> bool {
    exists|i: int| #[trigger] is_overdue(m, c, i)
}

/// Work `i` is overdue with the earliest deadline: when the clock jumped past
/// several deadlines, their work runs in deadline order.
pub open spec fn is_first<M: Model>(m: M, c: Cfg<M>, i: int) -> bool {
    is_overdue(m, c, i) && forall|k: int| #[trigger] is_overdue(m, c, k) ==> c.work[i].by.unwrap() <= c.work[k].by.unwrap()
}

// -------------------------------------------- steps: how the system evolves

/// A client sends a request. Observed.
pub open spec fn invoke<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Invoke { call, req }) => !c.calls.contains_key(call)
            && !overdue(m, c) && d == Config { calls: c.calls.insert(call, Call::InFlight(req)), ..c },
        _ => false,
    }
}

/// A client receives the response its call took effect with. Observed.
pub open spec fn ret<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Return { call, res }) => c.calls.contains_key(call)
            && c.calls[call] is Done && m.admits(c.calls[call]->Done_0, res) && !overdue(m, c)
            && d == Config { calls: c.calls.remove(call), ..c },
        _ => false,
    }
}

/// A client receives a dispatch that was sent and not yet received. Observed.
pub open spec fn receive<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Receive { msg }) => !overdue(m, c) && exists|i: int|
            0 <= i < c.sent.len() && #[trigger] c.sent[i] == msg && d == Config { sent: c.sent.remove(i), ..c },
        _ => false,
    }
}

/// A call in flight takes effect with one of its allowed outcomes. Silent.
pub open spec fn effect<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && !overdue(m, c) && exists|call: CallId, j: int|
        #![trigger c.calls[call], m.external(c.calls[call]->InFlight_0, c.state)[j]]
        c.calls.contains_key(call) && c.calls[call] is InFlight && {
            let outs = m.external(c.calls[call]->InFlight_0, c.state);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                calls: c.calls.insert(call, Call::Done(outs[j].resp)),
                work: start_all(c.work, outs[j].work, m.now(outs[j].next) as nat),
                sent: c.sent + outs[j].send,
                ..c
            }
        }
}

/// Pending internal work runs with one of its outcomes; while some work is
/// overdue, only overdue work runs. Silent.
pub open spec fn run<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && exists|i: int, j: int|
        #![trigger c.work[i], m.internal(c.work[i].req, c.state)[j]]
        0 <= i < c.work.len() && c.work[i].after <= clock(m, c) && (overdue(m, c) ==> is_first(m, c, i)) && {
            let outs = m.internal(c.work[i].req, c.state);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                work: start_all(c.work.remove(i), outs[j].work, m.now(outs[j].next) as nat),
                sent: c.sent + outs[j].send,
                ..c
            }
        }
}

/// The transition relation: from `c`, a step labeled `l` reaches `d`.
pub open spec fn step<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    invoke(m, c, l, d) || ret(m, c, l, d) || receive(m, c, l, d) || effect(m, c, l, d) || run(m, c, l, d)
}

// ------------------------------------- executions, and what they show a client

/// An execution: the steps taken from a starting configuration, each with the
/// configuration it leads to.
pub type Execution<M> = Seq<(Lab<M>, Cfg<M>)>;

/// The configuration before step `i`.
pub open spec fn before<M: Model>(first: Cfg<M>, steps: Execution<M>, i: int) -> Cfg<M> {
    if i == 0 { first } else { steps[i - 1].1 }
}

/// The system can take these steps, one after the other, starting from `first`.
pub open spec fn legal<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>) -> bool {
    forall|i: int| 0 <= i < steps.len() ==> #[trigger] step(m, before::<M>(first, steps, i), steps[i].0, steps[i].1)
}

/// What an execution shows a client: its observed events, in order. Silent
/// steps show nothing.
pub open spec fn project<M: Model>(steps: Execution<M>) -> Seq<Ev<M>>
    decreases steps.len(),
{
    if steps.len() == 0 {
        Seq::empty()
    } else {
        let rest = project::<M>(steps.subrange(1, steps.len() as int));
        match steps[0].0 {
            Label::Obs(e) => seq![e] + rest,
            Label::Silent => rest,
        }
    }
}

/// The system starts in `init`, with no calls in flight and the work the model
/// starts with scheduled on the initial clock.
pub open spec fn initial<M: Model>(m: M, init: M::State) -> Cfg<M> {
    Config { state: init, calls: Map::empty(), work: start_all(Seq::empty(), m.start(init), m.now(init) as nat), sent: Seq::empty() }
}

/// The trace is valid: some execution of the system, from `initial(m, init)`,
/// projected onto what clients observe, is exactly the trace.
pub open spec fn valid<M: Model>(m: M, init: M::State, trace: Seq<Ev<M>>) -> bool {
    exists|steps: Execution<M>|
        #![trigger legal(m, initial::<M>(m, init), steps), project::<M>(steps)]
        legal(m, initial::<M>(m, init), steps) && project::<M>(steps) == trace
}

// ------------------------------------------------------------------ theorem

/// Soundness, as the contract of the Rust checker: if it accepts a trace, the
/// trace is valid. Stated, not proved.
///
/// `Checker::new(m, init, Config::default()).check_certified(trace).is_ok()`
#[verifier::external_body]
pub fn check<M: Model>(m: &M, init: Ghost<M::State>, trace: &Vec<Ev<M>>) -> (accepted: bool)
    ensures
        accepted ==> valid(*m, init@, trace@),
{
    unimplemented!()
}

// --------------------------------------------------------- examples, proved

/// For every model, the empty trace is valid: the execution with no steps.
pub proof fn empty_trace_valid<M: Model>(m: M, init: M::State)
    ensures
        valid(m, init, Seq::<Ev<M>>::empty()),
{
    let steps = Execution::<M>::empty();
    assert(legal(m, initial::<M>(m, init), steps));
    assert(project::<M>(steps) =~= Seq::<Ev<M>>::empty());
}

/// A counter: `incr` takes effect and answers the new value.
pub struct Counter;

impl Model for Counter {
    type State = nat;
    type External = ();
    type Response = nat;
    type Internal = ();
    type Dispatch = ();

    open spec fn external(&self, req: (), n: nat) -> Seq<ExternalOutcome<nat, nat, (), ()>> {
        seq![ExternalOutcome { next: n + 1, resp: n + 1, work: Seq::empty(), send: Seq::empty() }]
    }

    open spec fn internal(&self, req: (), n: nat) -> Seq<InternalOutcome<nat, (), ()>> {
        Seq::empty()
    }

    open spec fn admits(&self, expected: nat, observed: nat) -> bool {
        expected == observed
    }

    open spec fn now(&self, n: nat) -> Time {
        0
    }

    open spec fn start(&self, n: nat) -> Seq<Sched<()>> {
        Seq::empty()
    }
}

/// Sent, then answered 1: valid. The execution is invoke (observed),
/// effect (silent), return (observed).
pub proof fn counter_trace_valid()
    ensures
        valid(
            Counter,
            0nat,
            seq![
                Event::Invoke { call: 7, req: () },
                Event::<(), nat, ()>::Return { call: 7, res: 1nat },
            ],
        ),
{
    let m = Counter;
    let c0 = initial::<Counter>(m, 0nat);
    let c1 = Config { calls: c0.calls.insert(7, Call::InFlight(())), ..c0 };
    let c2 = Config { state: 1nat, calls: c1.calls.insert(7, Call::Done(1nat)), work: start_all(c1.work, Seq::empty(), 0nat), sent: c1.sent + Seq::empty(), ..c1 };
    let c3 = Config { calls: c2.calls.remove(7), ..c2 };
    let l0 = Label::Obs(Event::Invoke { call: 7, req: () });
    let l1 = Label::<(), nat, ()>::Silent;
    let l2 = Label::Obs(Event::<(), nat, ()>::Return { call: 7, res: 1nat });
    let steps: Execution<Counter> = seq![(l0, c1), (l1, c2), (l2, c3)];
    // Nothing is ever overdue: there is no internal work.
    assert(!overdue(m, c0));
    assert(!overdue(m, c1));
    assert(!overdue(m, c2));
    assert(invoke(m, c0, l0, c1));
    assert(effect(m, c1, l1, c2)) by {
        assert(c1.calls[7] is InFlight);
        let outs = m.external(c1.calls[7]->InFlight_0, c1.state);
        assert(outs[0].next == 1nat && outs[0].resp == 1nat);
        assert(start_all(c1.work, outs[0].work, m.now(outs[0].next) as nat) =~= c1.work);
        assert(c2 == Config { state: outs[0].next, calls: c1.calls.insert(7, Call::Done(outs[0].resp)),
            work: start_all(c1.work, outs[0].work, m.now(outs[0].next) as nat), sent: c1.sent + outs[0].send, ..c1 });
    }
    assert(ret(m, c2, l2, c3));
    assert(before::<Counter>(c0, steps, 0) == c0);
    assert(before::<Counter>(c0, steps, 1) == c1);
    assert(before::<Counter>(c0, steps, 2) == c2);
    assert(legal(m, c0, steps));
    assert(project::<Counter>(steps) =~= seq![
        Event::Invoke { call: 7, req: () },
        Event::<(), nat, ()>::Return { call: 7, res: 1nat },
    ]) by {
        reveal_with_fuel(project, 4);
    }
}

} // verus!
