//! The soundness statement of the accordant checker, in Verus.
//!
//! How a system's evolution maps to what clients observe, as in
//! `lean/Accordant.lean`:
//!
//! * The system is a labeled transition system over configurations.
//! * Every step either produces an observation (a request sent, a response
//!   received, a dispatch received) or is silent (a call taking effect,
//!   internal work running, time passing).
//! * A trace is valid when some run from the start produces exactly those
//!   observations, in order, with any number of silent steps in between.
//!
//! The checker's contract, and the Lean-style theorem, say that whatever the
//! checker accepts is valid.
//!
//! This file states the theorem; it does not prove it. `check` is
//! `external_body` and the lemma is `admit()`ted.
//!
//! Not modeled here: request lifetimes (an unanswered call may take effect at
//! any later time, or never) and `assert_idle`.

use vstd::prelude::*;

verus! {

pub type Time = u64;

pub type CallId = u64;

// ------------------------------------------------------------- observations

/// What a client observes, and when.
pub enum Event<X, R, D> {
    /// The client sent a request.
    Invoke { at: Time, call: CallId, req: X },
    /// The client got the response to that call.
    Return { at: Time, call: CallId, res: R },
    /// The client got a dispatch the server sent on its own.
    Receive { at: Time, msg: D },
}

impl<X, R, D> Event<X, R, D> {
    pub open spec fn at(self) -> Time {
        match self {
            Event::Invoke { at, .. } => at,
            Event::Return { at, .. } => at,
            Event::Receive { at, .. } => at,
        }
    }
}

// -------------------------------------------------------------------- model

/// Internal work to start, and when it runs.
pub enum Sched<I> {
    /// From now on; must have happened by the time the system is idle.
    Later(I),
    /// Exactly at the given time.
    Timer(Time, I),
    /// Not before the given time; must have happened by the time the system is idle.
    After(Time, I),
    /// From now on; must have happened within the given duration.
    Within(Time, I),
    /// From now on, or never.
    Maybe(I),
}

/// One possible effect of a request.
pub struct ExternalOutcome<S, R, I, D> {
    pub next: S,
    pub res: R,
    pub spawn: Seq<Sched<I>>,
    pub send: Seq<D>,
}

/// One possible effect of internal work.
pub struct InternalOutcome<S, I, D> {
    pub next: S,
    pub spawn: Seq<Sched<I>>,
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
    spec fn external(&self, req: Self::External, state: Self::State, now: Time) -> Seq<
        ExternalOutcome<Self::State, Self::Response, Self::Internal, Self::Dispatch>,
    >;

    /// Internal work runs: every possible outcome. Empty: it can't run yet.
    spec fn internal(&self, req: Self::Internal, state: Self::State, now: Time) -> Seq<
        InternalOutcome<Self::State, Self::Internal, Self::Dispatch>,
    >;
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
    pub after: Time,
    /// Must have run before anything is observed at or after this time.
    pub by: Option<Time>,
    /// Must run at some point (false: `Maybe`).
    pub must: bool,
}

/// Everything about a run at one point, seen or not.
pub struct Config<S, X, R, I, D> {
    pub state: S,
    pub now: Time,
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

pub open spec fn max(a: Time, b: Time) -> Time {
    if a >= b { a } else { b }
}

pub open spec fn schedule<I>(s: Sched<I>, now: Time) -> Work<I> {
    match s {
        Sched::Later(req) => Work { req, after: now, by: None, must: true },
        Sched::Timer(at, req) => Work { req, after: max(at, now), by: Some(max(at, now)), must: true },
        Sched::After(at, req) => Work { req, after: max(at, now), by: None, must: true },
        Sched::Within(d, req) => Work { req, after: now, by: Some((now + d) as Time), must: true },
        Sched::Maybe(req) => Work { req, after: now, by: None, must: false },
    }
}

pub open spec fn start_all<I>(work: Seq<Work<I>>, spawn: Seq<Sched<I>>, now: Time) -> Seq<Work<I>> {
    work + spawn.map_values(|s: Sched<I>| schedule(s, now))
}

/// Work that can run now and whose deadline has come: it runs before anything
/// else happens. Work that can't run owes nothing.
pub open spec fn is_overdue<M: Model>(m: M, c: Cfg<M>, i: int) -> bool {
    0 <= i < c.work.len() && c.work[i].must && c.work[i].after <= c.now && match c.work[i].by {
        Some(by) => by <= c.now && m.internal(c.work[i].req, c.state, c.now).len() > 0,
        None => false,
    }
}

pub open spec fn overdue<M: Model>(m: M, c: Cfg<M>) -> bool {
    exists|i: int| #[trigger] is_overdue(m, c, i)
}

/// Time may move to `to` only if no work that can run is due before then.
pub open spec fn may_advance<M: Model>(m: M, c: Cfg<M>, to: Time) -> bool {
    to > c.now && forall|i: int|
        0 <= i < c.work.len() && c.work[i].must && #[trigger] c.work[i].by.is_some() && m.internal(
            c.work[i].req,
            c.state,
            c.now,
        ).len() > 0 ==> to <= c.work[i].by.unwrap()
}

// -------------------------------------------- steps: how the system evolves

/// A client sends a request. Observed.
pub open spec fn invoke<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Invoke { at, call, req }) => at == c.now && !c.calls.contains_key(call)
            && !overdue(m, c) && d == Config { calls: c.calls.insert(call, Call::InFlight(req)), ..c },
        _ => false,
    }
}

/// A client receives the response its call took effect with. Observed.
pub open spec fn ret<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Return { at, call, res }) => at == c.now && c.calls.contains_key(call)
            && c.calls[call] == Call::<M::External, M::Response>::Done(res) && !overdue(m, c)
            && d == Config { calls: c.calls.remove(call), ..c },
        _ => false,
    }
}

/// A client receives a dispatch that was sent and not yet received. Observed.
pub open spec fn receive<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Receive { at, msg }) => at == c.now && !overdue(m, c) && exists|i: int|
            0 <= i < c.sent.len() && #[trigger] c.sent[i] == msg && d == Config { sent: c.sent.remove(i), ..c },
        _ => false,
    }
}

/// A call in flight takes effect with one of its allowed outcomes. Silent.
pub open spec fn effect<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && !overdue(m, c) && exists|call: CallId, j: int|
        #![trigger c.calls[call], m.external(c.calls[call]->InFlight_0, c.state, c.now)[j]]
        c.calls.contains_key(call) && c.calls[call] is InFlight && {
            let outs = m.external(c.calls[call]->InFlight_0, c.state, c.now);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                calls: c.calls.insert(call, Call::Done(outs[j].res)),
                work: start_all(c.work, outs[j].spawn, c.now),
                sent: c.sent + outs[j].send,
                ..c
            }
        }
}

/// Pending internal work runs with one of its outcomes; while some work is
/// overdue, only overdue work runs. Silent.
pub open spec fn run<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && exists|i: int, j: int|
        #![trigger c.work[i], m.internal(c.work[i].req, c.state, c.now)[j]]
        0 <= i < c.work.len() && c.work[i].after <= c.now && (overdue(m, c) ==> is_overdue(m, c, i)) && {
            let outs = m.internal(c.work[i].req, c.state, c.now);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                work: start_all(c.work.remove(i), outs[j].spawn, c.now),
                sent: c.sent + outs[j].send,
                ..c
            }
        }
}

/// Time passes, but not past a deadline whose work could still run. Silent.
pub open spec fn advance<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && exists|t: Time| #[trigger] may_advance(m, c, t) && d == Config { now: t, ..c }
}

/// The transition relation: from `c`, a step labeled `l` reaches `d`.
pub open spec fn step<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    invoke(m, c, l, d) || ret(m, c, l, d) || receive(m, c, l, d) || effect(m, c, l, d) || run(m, c, l, d)
        || advance(m, c, l, d)
}

// ------------------------------------------------- runs and what they show

/// `configs[0] -labels[0]-> configs[1] -labels[1]-> ...`: a run of the model.
pub open spec fn is_run<M: Model>(m: M, configs: Seq<Cfg<M>>, labels: Seq<Lab<M>>) -> bool {
    configs.len() == labels.len() + 1 && forall|i: int|
        0 <= i < labels.len() ==> #[trigger] step(m, configs[i], labels[i], configs[i + 1])
}

/// What a run shows a client: its observations, in order; silent steps show nothing.
pub open spec fn visible<M: Model>(labels: Seq<Lab<M>>) -> Seq<Ev<M>>
    decreases labels.len(),
{
    if labels.len() == 0 {
        Seq::empty()
    } else {
        let rest = visible::<M>(labels.subrange(1, labels.len() as int));
        match labels[0] {
            Label::Obs(e) => seq![e] + rest,
            Label::Silent => rest,
        }
    }
}

pub open spec fn initial<M: Model>(init: M::State, start: Time) -> Cfg<M> {
    Config { state: init, now: start, calls: Map::empty(), work: Seq::empty(), sent: Seq::empty() }
}

/// The trace is valid: some run of the model, from `init` at `start`, shows
/// exactly these observations.
pub open spec fn valid<M: Model>(m: M, init: M::State, start: Time, trace: Seq<Ev<M>>) -> bool {
    exists|configs: Seq<Cfg<M>>, labels: Seq<Lab<M>>|
        #![trigger is_run(m, configs, labels), visible::<M>(labels)]
        is_run(m, configs, labels) && configs[0] == initial::<M>(init, start) && visible::<M>(labels) == trace
}

// ------------------------------------------------------------------ theorem

/// The checker's contract: what it accepts is valid.
#[verifier::external_body]
pub fn check<M: Model>(m: &M, init: Ghost<M::State>, start: Time, trace: &Vec<Ev<M>>) -> (accepted: bool)
    ensures
        accepted ==> valid(*m, init@, start, trace@),
{
    unimplemented!()
}

/// The checker's verdict, as a predicate (Lean's `Accepted`).
pub uninterp spec fn accepted<M: Model>(m: M, init: M::State, start: Time, trace: Seq<Ev<M>>) -> bool;

/// Soundness: whatever the checker accepts is valid. Stated, not proved.
pub proof fn accepted_implies_valid<M: Model>(m: M, init: M::State, start: Time, trace: Seq<Ev<M>>)
    requires
        accepted(m, init, start, trace),
    ensures
        valid(m, init, start, trace),
{
    admit();
}

// ------------------------------------------------------ sanity checks, proved

/// For every model, the empty trace is valid.
pub proof fn empty_trace_valid<M: Model>(m: M, init: M::State, start: Time)
    ensures
        valid(m, init, start, Seq::<Ev<M>>::empty()),
{
    let configs = seq![initial::<M>(init, start)];
    let labels = Seq::<Lab<M>>::empty();
    assert(is_run(m, configs, labels));
    assert(visible::<M>(labels) =~= Seq::<Ev<M>>::empty());
}

/// A one-call counter: `incr` takes effect and answers the new value.
pub struct Counter;

impl Model for Counter {
    type State = nat;
    type External = ();
    type Response = nat;
    type Internal = ();
    type Dispatch = ();

    open spec fn external(&self, req: (), n: nat, now: Time) -> Seq<ExternalOutcome<nat, nat, (), ()>> {
        seq![ExternalOutcome { next: n + 1, res: n + 1, spawn: Seq::empty(), send: Seq::empty() }]
    }

    open spec fn internal(&self, req: (), n: nat, now: Time) -> Seq<InternalOutcome<nat, (), ()>> {
        Seq::empty()
    }
}

/// Sent at 0, answered 1 at 0: valid. The run is invoke (seen), effect (silent),
/// return (seen).
pub proof fn counter_trace_valid()
    ensures
        valid(
            Counter,
            0nat,
            0,
            seq![
                Event::Invoke { at: 0, call: 7, req: () },
                Event::<(), nat, ()>::Return { at: 0, call: 7, res: 1nat },
            ],
        ),
{
    let m = Counter;
    let c0 = initial::<Counter>(0nat, 0);
    let c1 = Config { calls: c0.calls.insert(7, Call::InFlight(())), ..c0 };
    let c2 = Config { state: 1nat, calls: c1.calls.insert(7, Call::Done(1nat)), work: start_all(c1.work, Seq::empty(), 0), sent: c1.sent + Seq::empty(), ..c1 };
    let c3 = Config { calls: c2.calls.remove(7), ..c2 };
    let l0 = Label::Obs(Event::Invoke { at: 0, call: 7, req: () });
    let l1 = Label::<(), nat, ()>::Silent;
    let l2 = Label::Obs(Event::<(), nat, ()>::Return { at: 0, call: 7, res: 1nat });
    let configs = seq![c0, c1, c2, c3];
    let labels = seq![l0, l1, l2];
    // Nothing is ever overdue: there is no internal work.
    assert(!overdue(m, c0));
    assert(!overdue(m, c1));
    assert(!overdue(m, c2));
    assert(invoke(m, c0, l0, c1));
    assert(effect(m, c1, l1, c2)) by {
        assert(c1.calls[7] is InFlight);
        let outs = m.external(c1.calls[7]->InFlight_0, c1.state, c1.now);
        assert(outs[0].next == 1nat && outs[0].res == 1nat);
        assert(start_all(c1.work, outs[0].spawn, c1.now) =~= c1.work);
        assert(c2 == Config { state: outs[0].next, calls: c1.calls.insert(7, Call::Done(outs[0].res)),
            work: start_all(c1.work, outs[0].spawn, c1.now), sent: c1.sent + outs[0].send, ..c1 });
    }
    assert(ret(m, c2, l2, c3));
    assert(is_run(m, configs, labels));
    assert(visible::<Counter>(labels) =~= seq![
        Event::Invoke { at: 0, call: 7, req: () },
        Event::<(), nat, ()>::Return { at: 0, call: 7, res: 1nat },
    ]) by {
        reveal_with_fuel(visible, 4);
    }
}

} // verus!
