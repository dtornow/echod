//! What the checker promises, in Verus.
//!
//! In one sentence:
//!
//! > OK means some execution of the system, projected onto what clients
//! > observe, is exactly the trace; KO means no execution is; UNKNOWN means
//! > the checker can't tell.
//!
//! As the contract of a Rust function, at the bottom of this file:
//!
//! ```text
//! fn check(m, init, trace) -> (v: Verdict)
//!     ensures v is Ok ==> valid(m, init, trace),
//!             v is Ko ==> !valid(m, init, trace)
//!
//! valid(m, init, trace) :=
//!     exists steps. legal(m, initial(init), steps) && project(steps) == trace
//! ```
//!
//! Everything above `check` defines its words: a [`Config`] (the system at one
//! point, seen or not), [`step`] (how the system evolves, each step observed
//! or silent), [`legal`] (steps the system can actually take), [`project`]
//! (what an execution shows a client). It is specification only: nothing here
//! runs. [`Model`] is the system, with its `spec` twins of `external`,
//! `internal` and `now`.
//!
//! The OK line is proved: `certify` (`certificate.rs`) ensures that a
//! certificate it accepts makes the trace valid, and `Checker::check_certified`
//! answers OK only after `certify` accepts. The KO line is not proved anywhere:
//! it rests on the search being exhaustive.

use vstd::prelude::*;

use crate::{CallId, Event, Model, Sched, Time};

verus! {

// ------------------------------------------------------------------ outcomes

/// [`crate::ExternalOutcome`] as the proofs see it: its vectors as sequences.
pub struct ExternalOutcomeV<S, R, I, D> {
    pub next: S,
    pub resp: R,
    pub work: Seq<Sched<I>>,
    pub send: Seq<D>,
}

/// [`crate::InternalOutcome`] as the proofs see it: its vectors as sequences.
pub struct InternalOutcomeV<S, I, D> {
    pub next: S,
    pub work: Seq<Sched<I>>,
    pub send: Seq<D>,
}

pub type Ev<M> = Event<<M as Model>::External, <M as Model>::Response, <M as Model>::Dispatch>;

// ------------------------------------------------------------ configurations

/// A call the client has sent and not yet seen answered.
pub enum Call<X, R> {
    /// Not yet taken effect.
    InFlight(X),
    /// Taken effect; the client will see this response.
    Done(R),
}

/// Internal work started and not yet run.
#[derive(Clone, Debug, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Work<I> {
    pub req: I,
    /// Can't run before this time.
    pub after: Time,
    /// Must have run by this time, if it can run then.
    pub due: Option<Time>,
    /// Must run at some point.
    pub must: bool,
}

/// Everything about the system at one point, seen or not.
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

pub open spec fn max(a: Time, b: Time) -> Time {
    if a >= b { a } else { b }
}

/// Work scheduled at `now`: a timer at `t` runs at `t`, or right away if `t`
/// has passed.
pub open spec fn schedule<I>(now: Time, s: Sched<I>) -> Work<I> {
    match s {
        Sched::Later(req) => Work { req, after: now, due: None, must: true },
        Sched::Timer(t, req) => Work { req, after: max(t, now), due: Some(max(t, now)), must: true },
    }
}

pub open spec fn start_all<I>(work: Seq<Work<I>>, new: Seq<Sched<I>>, now: Time) -> Seq<Work<I>> {
    work + new.map_values(|s: Sched<I>| schedule(now, s))
}

pub open spec fn clock<M: Model>(m: M, c: Cfg<M>) -> Time {
    m.spec_now(c.state)
}

/// Work whose deadline has come on the model's clock, and that can run: it runs
/// before anything else happens.
pub open spec fn is_overdue<M: Model>(m: M, c: Cfg<M>, i: int) -> bool {
    0 <= i < c.work.len() && c.work[i].must && c.work[i].after <= clock(m, c) && match c.work[i].due {
        Some(due) => due <= clock(m, c) && m.spec_internal(c.work[i].req, c.state).len() > 0,
        None => false,
    }
}

pub open spec fn overdue<M: Model>(m: M, c: Cfg<M>) -> bool {
    exists|i: int| #[trigger] is_overdue(m, c, i)
}

/// Both have a deadline, and `w`'s is no later.
pub open spec fn due_le<I>(w: Work<I>, v: Work<I>) -> bool {
    match (w.due, v.due) {
        (Some(d), Some(e)) => d <= e,
        _ => false,
    }
}

/// Work `i` is overdue with the earliest deadline: when the clock jumped past
/// several deadlines, their work runs in deadline order.
pub open spec fn is_first<M: Model>(m: M, c: Cfg<M>, i: int) -> bool {
    is_overdue(m, c, i) && forall|k: int| #[trigger] is_overdue(m, c, k) ==> due_le(c.work[i], c.work[k])
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
            && c.calls[call] is Done && c.calls[call]->Done_0 == res && !overdue(m, c)
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
        #![trigger c.calls[call], m.spec_external(c.calls[call]->InFlight_0, c.state)[j]]
        c.calls.contains_key(call) && c.calls[call] is InFlight && {
            let outs = m.spec_external(c.calls[call]->InFlight_0, c.state);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                calls: c.calls.insert(call, Call::Done(outs[j].resp)),
                work: start_all(c.work, outs[j].work, m.spec_now(outs[j].next)),
                sent: c.sent + outs[j].send,
                ..c
            }
        }
}

/// Pending internal work runs with one of its outcomes; while some work is
/// overdue, only the overdue work with the earliest deadline runs. Silent.
pub open spec fn run<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && exists|i: int, j: int|
        #![trigger c.work[i], m.spec_internal(c.work[i].req, c.state)[j]]
        0 <= i < c.work.len() && c.work[i].after <= clock(m, c) && (overdue(m, c) ==> is_first(m, c, i)) && {
            let outs = m.spec_internal(c.work[i].req, c.state);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                work: start_all(c.work.remove(i), outs[j].work, m.spec_now(outs[j].next)),
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

/// The configuration before step `i` (after the last step, for `i == steps.len()`).
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
        let shown = project::<M>(steps.drop_last());
        match steps.last().0 {
            Label::Obs(e) => shown.push(e),
            Label::Silent => shown,
        }
    }
}

/// The system starts in `init`, with nothing in flight.
pub open spec fn initial<M: Model>(init: M::State) -> Cfg<M> {
    Config { state: init, calls: Map::empty(), work: Seq::empty(), sent: Seq::empty() }
}

/// The trace is valid: some execution of the system, from `initial(init)`,
/// projected onto what clients observe, is exactly the trace.
pub open spec fn valid<M: Model>(m: M, init: M::State, trace: Seq<Ev<M>>) -> bool {
    exists|steps: Execution<M>|
        #![trigger legal(m, initial::<M>(init), steps), project::<M>(steps)]
        legal(m, initial::<M>(init), steps) && project::<M>(steps) == trace
}

// ------------------------------------------------------------------ theorem

/// What the checker answers about a trace: [`crate::Verdict`] without its
/// payloads.
pub enum Verdict {
    /// Some execution of the system shows exactly the trace.
    Ok,
    /// No execution of the system shows the trace.
    Ko,
    /// The checker can't say (it gave up).
    Unknown,
}

/// The trace checker, with certificates, under the contract it is held to:
/// OK only for valid traces, KO only for invalid ones, and UNKNOWN whenever it
/// can't tell. Verus takes the contract on trust (`external_body`). OK is
/// justified: `check_certified` answers OK only after [`crate::certify`]
/// accepts a certificate, and `certify` is proved to accept only valid
/// traces. KO rests on the search.
#[verifier::external_body]
pub fn check<M: Model + Clone>(m: &M, init: M::State, trace: &[Ev<M>]) -> (v: Verdict)
    ensures
        v is Ok ==> valid(*m, init, trace@),
        v is Ko ==> !valid(*m, init, trace@),
{
    let cfg = crate::Config { certify: true, ..crate::Config::default() };
    let mut checker = crate::Checker::new(m.clone(), init, cfg);
    match checker.check_certified(trace.iter().cloned()) {
        Ok(_) => Verdict::Ok,
        Err(v) if v.unknown => Verdict::Unknown,
        Err(_) => Verdict::Ko,
    }
}

/// For every model, the empty trace is valid: the execution with no steps.
pub proof fn empty_trace_valid<M: Model>(m: M, init: M::State)
    ensures
        valid(m, init, Seq::<Ev<M>>::empty()),
{
    let steps = Execution::<M>::empty();
    assert(legal(m, initial::<M>(init), steps));
    assert(project::<M>(steps) =~= Seq::<Ev<M>>::empty());
}

} // verus!
