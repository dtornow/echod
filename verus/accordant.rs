//! The soundness statement of the accordant checker, in Verus.
//!
//! A trace is what clients observe. It is valid when some run of the model
//! produces exactly that trace: a sequence of moves that interleaves the
//! observations with everything nobody sees (calls taking effect, internal work
//! running, time passing). The checker's contract, and the Lean-style theorem,
//! say that whatever the checker accepts is valid.
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
    /// How many observations of the trace this run has produced so far.
    pub seen: nat,
}

pub type Cfg<M> = Config<
    <M as Model>::State,
    <M as Model>::External,
    <M as Model>::Response,
    <M as Model>::Internal,
    <M as Model>::Dispatch,
>;

/// One move of a run: the next observation, or something nobody sees.
pub enum Move {
    /// The next observation of the trace happens.
    Observe,
    /// A call in flight takes effect, with the `choice`-th allowed outcome.
    Effect { call: CallId, choice: nat },
    /// The `item`-th pending internal work runs, with the `choice`-th outcome.
    Run { item: nat, choice: nat },
    /// Time passes.
    Advance { to: Time },
}

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

/// The next observation, if it happens now from `c`.
pub open spec fn observe<M: Model>(m: M, c: Cfg<M>, e: Ev<M>) -> Option<Cfg<M>> {
    if e.at() != c.now || overdue(m, c) {
        None
    } else {
        match e {
            Event::Invoke { call, req, .. } => if c.calls.contains_key(call) {
                None
            } else {
                Some(Config { calls: c.calls.insert(call, Call::InFlight(req)), seen: c.seen + 1, ..c })
            },
            Event::Return { call, res, .. } => if c.calls.contains_key(call) && c.calls[call]
                == Call::<M::External, M::Response>::Done(res) {
                Some(Config { calls: c.calls.remove(call), seen: c.seen + 1, ..c })
            } else {
                None
            },
            Event::Receive { msg, .. } => if c.sent.contains(msg) {
                let i = choose|i: int| 0 <= i < c.sent.len() && c.sent[i] == msg;
                Some(Config { sent: c.sent.remove(i), seen: c.seen + 1, ..c })
            } else {
                None
            },
        }
    }
}

/// One move from `c`, or `None` if the move isn't allowed there.
pub open spec fn step<M: Model>(m: M, c: Cfg<M>, mv: Move, trace: Seq<Ev<M>>) -> Option<Cfg<M>> {
    match mv {
        Move::Observe => if c.seen < trace.len() {
            observe(m, c, trace[c.seen as int])
        } else {
            None
        },
        Move::Effect { call, choice } => {
            if !c.calls.contains_key(call) || overdue(m, c) {
                None
            } else {
                match c.calls[call] {
                    Call::InFlight(req) => {
                        let outs = m.external(req, c.state, c.now);
                        if choice < outs.len() {
                            let o = outs[choice as int];
                            Some(
                                Config {
                                    state: o.next,
                                    calls: c.calls.insert(call, Call::Done(o.res)),
                                    work: start_all(c.work, o.spawn, c.now),
                                    sent: c.sent + o.send,
                                    ..c
                                },
                            )
                        } else {
                            None
                        }
                    },
                    Call::Done(_) => None,
                }
            }
        },
        Move::Run { item, choice } => {
            let i = item as int;
            if i >= c.work.len() || c.work[i].after > c.now || (overdue(m, c) && !is_overdue(m, c, i)) {
                None
            } else {
                let outs = m.internal(c.work[i].req, c.state, c.now);
                if choice < outs.len() {
                    let o = outs[choice as int];
                    Some(
                        Config {
                            state: o.next,
                            work: start_all(c.work.remove(i), o.spawn, c.now),
                            sent: c.sent + o.send,
                            ..c
                        },
                    )
                } else {
                    None
                }
            }
        },
        Move::Advance { to } => if may_advance(m, c, to) {
            Some(Config { now: to, ..c })
        } else {
            None
        },
    }
}

/// Plays `moves` from `c` against `trace`; `None` if some move isn't allowed.
pub open spec fn replay<M: Model>(m: M, c: Cfg<M>, moves: Seq<Move>, trace: Seq<Ev<M>>) -> Option<Cfg<M>>
    decreases moves.len(),
{
    if moves.len() == 0 {
        Some(c)
    } else {
        match step(m, c, moves[0], trace) {
            Some(next) => replay(m, next, moves.subrange(1, moves.len() as int), trace),
            None => None,
        }
    }
}

pub open spec fn initial<M: Model>(init: M::State, start: Time) -> Cfg<M> {
    Config { state: init, now: start, calls: Map::empty(), work: Seq::empty(), sent: Seq::empty(), seen: 0 }
}

/// The trace is valid: some run of the model, from `init` at time `start`,
/// produces exactly these observations.
pub open spec fn valid<M: Model>(m: M, init: M::State, start: Time, trace: Seq<Ev<M>>) -> bool {
    exists|moves: Seq<Move>|
        #![trigger replay(m, initial::<M>(init, start), moves, trace)]
        replay(m, initial::<M>(init, start), moves, trace) is Some && replay(
            m,
            initial::<M>(init, start),
            moves,
            trace,
        )->Some_0.seen == trace.len()
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

/// Lean's `accepted_trace_implies_valid_trace`.
pub proof fn accepted_trace_implies_valid_trace<M: Model>(
    m: M,
    init: M::State,
    start: Time,
    trace: Seq<Ev<M>>,
)
    requires
        accepted(m, init, start, trace),
    ensures
        valid(m, init, start, trace),
{
    admit();
}

// ------------------------------------------------------------ sanity checks

/// Proved, not admitted: no observations are explained by the empty run.
pub proof fn the_empty_trace_is_valid<M: Model>(m: M, init: M::State, start: Time)
    ensures
        valid(m, init, start, Seq::<Ev<M>>::empty()),
{
    let moves = Seq::<Move>::empty();
    assert(replay(m, initial::<M>(init, start), moves, Seq::<Ev<M>>::empty()) == Some(initial::<M>(init, start)));
}

} // verus!
