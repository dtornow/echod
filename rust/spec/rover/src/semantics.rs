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
//! runs. [`Model`] is the system, with its `spec` twins of `external` and
//! `internal`.
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

/// An external op a client sent, until it returns.
pub struct ExternalOp<X, R> {
    pub req: X,
    /// `None` while pending; `Some` once settled: the client will see this.
    pub res: Option<R>,
}

/// Everything about the system at one point, seen or not: the model's state,
/// and what the model doesn't know about.
pub struct Config<S, X, R, I, D> {
    pub state: S,
    /// The external ops outstanding, by call id. (Lean keeps a list of
    /// `{id, req, res}` with distinct ids; the same thing.)
    pub externals: Map<CallId, ExternalOp<X, R>>,
    /// The internal ops scheduled, each with when it runs, on the clock.
    pub internals: Seq<Sched<I>>,
    /// Dispatches sent and not yet received.
    pub sent: Seq<D>,
    /// The system's clock. The model reads it; only [`tick`] moves it.
    pub now: Time,
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

/// An internal op as it joins the queue. Its timer keeps the instant it names,
/// even when that instant is already past: it is overdue, earliest first.
pub open spec fn schedule<I>(now: Time, s: Sched<I>) -> Sched<I> {
    let _ = now;
    s
}

pub open spec fn start_all<I>(internals: Seq<Sched<I>>, new: Seq<Sched<I>>, now: Time) -> Seq<Sched<I>> {
    internals + new.map_values(|s: Sched<I>| schedule(now, s))
}

pub open spec fn req_of<I>(s: Sched<I>) -> I {
    match s {
        Sched::Later(req) => req,
        Sched::Timer(_, req) => req,
    }
}

/// The time a timer is due; a `Later` has none.
pub open spec fn due<I>(s: Sched<I>) -> Option<Time> {
    match s {
        Sched::Later(_) => None,
        Sched::Timer(t, _) => Some(t),
    }
}

/// Add one derived item unless the pending queue already contains it.
pub open spec fn insert_missing<I>(pending: Seq<Sched<I>>, item: Sched<I>) -> Seq<Sched<I>> {
    if pending.contains(item) { pending } else { pending.push(item) }
}

/// Materialize state-derived work in its model-defined order, without
/// duplicating an item already pending or derived earlier.
pub open spec fn augment<I>(pending: Seq<Sched<I>>, derived: Seq<Sched<I>>) -> Seq<Sched<I>>
    decreases derived.len(),
{
    if derived.len() == 0 {
        pending
    } else {
        insert_missing(augment(pending, derived.drop_last()), derived.last())
    }
}

pub proof fn lemma_augment_preserves<I>(
    pending: Seq<Sched<I>>,
    derived: Seq<Sched<I>>,
    item: Sched<I>,
)
    requires
        pending.contains(item),
    ensures
        augment(pending, derived).contains(item),
    decreases derived.len(),
{
    if derived.len() == 0 {
        assert(augment(pending, derived) == pending);
    } else {
        lemma_augment_preserves(pending, derived.drop_last(), item);
        let before = augment(pending, derived.drop_last());
        let i = choose|i: int| 0 <= i < before.len() && before[i] == item;
        if !before.contains(derived.last()) {
            assert(0 <= i < before.push(derived.last()).len());
            assert(before.push(derived.last())[i] == item);
            assert(exists|j: int|
                0 <= j < before.push(derived.last()).len()
                    && before.push(derived.last())[j] == item);
        }
        assert(augment(pending, derived)
            == insert_missing(before, derived.last()));
    }
}

pub proof fn lemma_augment_adds<I>(
    pending: Seq<Sched<I>>,
    derived: Seq<Sched<I>>,
    item: Sched<I>,
)
    requires
        derived.contains(item),
    ensures
        augment(pending, derived).contains(item),
    decreases derived.len(),
{
    if derived.len() == 0 {
        assert(!derived.contains(item));
    } else {
        let i = choose|i: int| 0 <= i < derived.len() && derived[i] == item;
        if i < derived.len() - 1 {
            assert(0 <= i < derived.drop_last().len());
            assert(derived.drop_last()[i] == item);
            assert(derived.drop_last().contains(item));
            lemma_augment_adds(pending, derived.drop_last(), item);
            lemma_augment_preserves(
                augment(pending, derived.drop_last()),
                seq![derived.last()],
                item,
            );
        } else {
            assert(i == derived.len() - 1);
            assert(derived.last() == item);
            let before = augment(pending, derived.drop_last());
            if !before.contains(item) {
                let j = before.len() as int;
                assert(0 <= j < before.push(item).len());
                assert(before.push(item)[j] == item);
                assert(exists|k: int| 0 <= k < before.push(item).len()
                    && before.push(item)[k] == item);
            }
        }
        let before = augment(pending, derived.drop_last());
        assert(before.contains(item) || derived.last() == item);
        if before.contains(derived.last()) {
            assert(before.contains(item));
        } else if before.contains(item) {
            let j = choose|j: int| 0 <= j < before.len() && before[j] == item;
            assert(0 <= j < before.push(derived.last()).len());
            assert(before.push(derived.last())[j] == item);
        } else {
            let j = before.len() as int;
            assert(derived.last() == item);
            assert(0 <= j < before.push(derived.last()).len());
            assert(before.push(derived.last())[j] == item);
        }
        assert(insert_missing(before, derived.last()).contains(item));
        assert(augment(pending, derived)
            == insert_missing(augment(pending, derived.drop_last()), derived.last()));
    }
}

pub proof fn lemma_augment_idempotent<I>(
    pending: Seq<Sched<I>>,
    derived: Seq<Sched<I>>,
)
    ensures
        augment(augment(pending, derived), derived) == augment(pending, derived),
    decreases derived.len(),
{
    assert forall|item: Sched<I>| derived.contains(item) implies
        augment(pending, derived).contains(item) by {
        lemma_augment_adds(pending, derived, item);
    }
    lemma_augment_noop(augment(pending, derived), derived);
}

pub proof fn lemma_augment_noop<I>(
    pending: Seq<Sched<I>>,
    derived: Seq<Sched<I>>,
)
    requires
        forall|item: Sched<I>| derived.contains(item) ==> pending.contains(item),
    ensures
        augment(pending, derived) == pending,
    decreases derived.len(),
{
    if derived.len() != 0 {
        assert forall|item: Sched<I>| derived.drop_last().contains(item) implies
            pending.contains(item) by {};
        lemma_augment_noop(pending, derived.drop_last());
        assert(pending.contains(derived.last()));
    }
}

/// Pending work as the model sees it: explicitly queued items followed by
/// state-derived items that are not already present.
pub open spec fn effective<M: Model>(m: M, c: Cfg<M>) -> Seq<Sched<M::Internal>> {
    augment(c.internals, m.spec_due(c.state, c.now))
}

/// Whether the op may run at `now`.
pub open spec fn ready<I>(now: Time, s: Sched<I>) -> bool {
    match s {
        Sched::Later(_) => true,
        Sched::Timer(t, _) => t <= now,
    }
}

/// A timer whose time has come and that can run: it runs before anything
/// else happens.
pub open spec fn is_overdue<M: Model>(m: M, c: Cfg<M>, i: int) -> bool {
    0 <= i < effective(m, c).len() && match effective(m, c)[i] {
        Sched::Timer(t, req) => t <= c.now && m.spec_internal(req, c.state, c.now).len() > 0,
        Sched::Later(_) => false,
    }
}

pub open spec fn overdue<M: Model>(m: M, c: Cfg<M>) -> bool {
    exists|i: int| #[trigger] is_overdue(m, c, i)
}

/// Both are timers, and `w`'s is due no later.
pub open spec fn due_le<I>(w: Sched<I>, v: Sched<I>) -> bool {
    match (due(w), due(v)) {
        (Some(d), Some(e)) => d <= e,
        _ => false,
    }
}

/// Op `i` is overdue with the earliest deadline: when the clock jumped past
/// several deadlines, their ops run in deadline order.
pub open spec fn is_first<M: Model>(m: M, c: Cfg<M>, i: int) -> bool {
    is_overdue(m, c, i) && forall|k: int| #[trigger] is_overdue(m, c, k) ==>
        due_le(effective(m, c)[i], effective(m, c)[k])
}

// -------------------------------------------- steps: how the system evolves

/// A client sends a request. Observed.
pub open spec fn invoke<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Invoke { call, req }) => !c.externals.contains_key(call)
            && !overdue(m, c)
            && d == Config { externals: c.externals.insert(call, ExternalOp { req, res: None }), ..c },
        _ => false,
    }
}

/// A client receives the response its call settled with. Observed.
pub open spec fn ret<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Return { call, res }) => c.externals.contains_key(call)
            && c.externals[call].res == Some(res) && !overdue(m, c)
            && d == Config { externals: c.externals.remove(call), ..c },
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

/// The clock moves forward. Observed: the trace records it. Work due by the
/// new time is then overdue, and runs before anything else is observed.
pub open spec fn tick<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    match l {
        Label::Obs(Event::Clock { at }) => c.now <= at && !overdue(m, c) && d == Config { now: at, ..c },
        _ => false,
    }
}

/// A pending external op settles with one of its allowed outcomes. Silent.
pub open spec fn effect<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && !overdue(m, c) && exists|call: CallId, j: int|
        #![trigger c.externals[call], m.spec_external(c.externals[call].req, c.state, c.now)[j]]
        c.externals.contains_key(call) && c.externals[call].res is None && {
            let outs = m.spec_external(c.externals[call].req, c.state, c.now);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                externals: c.externals.insert(call, ExternalOp { req: c.externals[call].req, res: Some(outs[j].resp) }),
                internals: start_all(effective(m, c), outs[j].work, c.now),
                sent: c.sent + outs[j].send,
                ..c
            }
        }
}

/// An internal op whose time has come runs with one of its outcomes; while
/// some op is overdue, only an overdue op with the earliest deadline runs.
/// Silent.
pub open spec fn run<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    l is Silent && exists|i: int, j: int|
        #![trigger effective(m, c)[i], m.spec_internal(req_of(effective(m, c)[i]), c.state, c.now)[j]]
        0 <= i < effective(m, c).len() && ready(c.now, effective(m, c)[i])
            && (overdue(m, c) ==> is_first(m, c, i)) && {
            let outs = m.spec_internal(req_of(effective(m, c)[i]), c.state, c.now);
            0 <= j < outs.len() && d == Config {
                state: outs[j].next,
                internals: start_all(effective(m, c).remove(i), outs[j].work, c.now),
                sent: c.sent + outs[j].send,
                ..c
            }
        }
}

/// The transition relation: from `c`, a step labeled `l` reaches `d`.
pub open spec fn step<M: Model>(m: M, c: Cfg<M>, l: Lab<M>, d: Cfg<M>) -> bool {
    invoke(m, c, l, d) || ret(m, c, l, d) || receive(m, c, l, d) || tick(m, c, l, d)
        || effect(m, c, l, d) || run(m, c, l, d)
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

/// The system starts in `init`, with nothing in flight, at time 0.
pub open spec fn initial<M: Model>(init: M::State) -> Cfg<M> {
    Config { state: init, externals: Map::empty(), internals: Seq::empty(), sent: Seq::empty(), now: 0 }
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
