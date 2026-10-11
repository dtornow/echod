//! Certificates: checking an execution someone found.
//!
//! Finding an execution is hard: the checker searches. Checking one is easy:
//! walk it, one step at a time. The trace already has the observed steps; a
//! certificate adds the silent ones the checker found: for each event, which
//! calls took effect and which work ran just before it, with which outcomes.
//! [`certify`] rebuilds the configurations and fails on the first step the
//! system can't make.
//!
//! The soundness of the checker rests on this file alone, not on the search,
//! and this file is verified: `certify` ensures that a certificate it accepts
//! makes the trace valid ([`semantics::valid`]), because each step of the
//! replay ensures it is a step the system can take ([`semantics::step`]). The
//! lemmas are in `proof.rs`; what is trusted beyond vstd, in `trusted.rs`.

use std::collections::{BTreeSet, HashMap};

use vstd::prelude::*;

#[allow(unused_imports)] // some only name specifications, erased in a plain build
use crate::semantics::{self, Call, Cfg, Execution, Label, Work};
use crate::{CallId, Event, Model, Sched, Time};

mod proof;
mod trusted;

use trusted::{copy, same};

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// A silent step, as a certificate names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Silent {
    /// The call takes effect with the `j`-th of its outcomes.
    Effect { call: CallId, j: usize },
    /// The `i`-th pending work runs with the `j`-th of its outcomes.
    Run { i: usize, j: usize },
}

/// A certificate: for each event of the trace, the silent steps just before it.
pub type Certificate = Vec<Vec<Silent>>;

pub type EventOf<M> = Event<<M as Model>::External, <M as Model>::Response, <M as Model>::Dispatch>;

/// Whether `cert` explains `trace`: from `init`, each event's silent steps and
/// then the event itself are steps the system can make. `Err(k)`: the steps up
/// to event `k` can't be made (or the certificate stops before it).
///
/// Verified: `Ok(())` means the trace is valid.
#[allow(clippy::needless_range_loop)] // index loops, for Verus
pub fn certify<M: Model>(m: &M, init: M::State, trace: &[EventOf<M>], cert: &[Vec<Silent>]) -> (r: Result<(), usize>)
    ensures
        r is Ok ==> semantics::valid(*m, init, trace@),
{
    let mut c = Config::initial(m, init);
    // For the proof: the execution replayed so far.
    let ghost mut steps: Execution<M> = Seq::empty();
    for k in 0..trace.len()
        invariant
            c.m == m,
            semantics::legal(*m, semantics::initial::<M>(init), steps),
            semantics::before::<M>(semantics::initial::<M>(init), steps, steps.len() as int) == c@,
            semantics::project::<M>(steps) == trace@.subrange(0, k as int),
    {
        if k >= cert.len() {
            return Err(k);
        }
        let silent = &cert[k];
        for s in 0..silent.len()
            invariant
                c.m == m,
                semantics::legal(*m, semantics::initial::<M>(init), steps),
                semantics::before::<M>(semantics::initial::<M>(init), steps, steps.len() as int) == c@,
                semantics::project::<M>(steps) == trace@.subrange(0, k as int),
        {
            if let Err(()) = c.silent(silent[s]) {
                return Err(k);
            }
            proof {
                proof::silent_step(*m, semantics::initial::<M>(init), steps, c@);
                steps = steps.push((Label::Silent, c@));
            }
        }
        if let Err(()) = c.observe(&trace[k]) {
            return Err(k);
        }
        proof {
            proof::observed_step(*m, semantics::initial::<M>(init), steps, trace@, k as int, c@);
            steps = steps.push((Label::Obs(trace@[k as int]), c@));
        }
    }
    proof {
        assert(trace@.subrange(0, trace@.len() as int) =~= trace@);
        proof::accepted_valid(*m, init, steps, trace@);
    }
    Ok(())
}

/// Everything about the system at one point, seen or not. Its view (`@`) is
/// the [`semantics::Config`] the proofs talk about.
pub(crate) struct Config<'m, M: Model> {
    pub(crate) m: &'m M,
    pub(crate) state: M::State,
    pub(crate) calls: HashMap<CallId, Call<M::External, M::Response>>,
    pub(crate) work: Vec<Work<M::Internal>>,
    pub(crate) sent: Vec<M::Dispatch>,
    pub(crate) now: Time,
}

impl<'m, M: Model> View for Config<'m, M> {
    type V = Cfg<M>;

    open(crate) spec fn view(&self) -> Cfg<M> {
        semantics::Config { state: self.state, calls: self.calls@, work: self.work@, sent: self.sent@, now: self.now }
    }
}

fn due_le<I>(w: &Work<I>, v: &Work<I>) -> (r: bool)
    ensures
        r == semantics::due_le(*w, *v),
{
    match (w.due, v.due) {
        (Some(d), Some(e)) => d <= e,
        _ => false,
    }
}

fn max(a: Time, b: Time) -> (r: Time)
    ensures
        r == semantics::max(a, b),
{
    if a >= b { a } else { b }
}

fn schedule<I>(now: Time, s: Sched<I>) -> (w: Work<I>)
    ensures
        w == semantics::schedule(now, s),
{
    match s {
        Sched::Later(req) => Work { req, after: now, due: None, must: true },
        Sched::Timer(t, req) => Work { req, after: max(t, now), due: Some(max(t, now)), must: true },
    }
}

impl<'m, M: Model> Config<'m, M> {
    pub(crate) fn initial(m: &'m M, init: M::State) -> (c: Self)
        ensures
            c@ == semantics::initial::<M>(init),
            c.m == m,
    {
        Config { m, state: init, calls: HashMap::new(), work: Vec::new(), sent: Vec::new(), now: 0 }
    }

    /// Work `i`'s deadline has come on the clock and it can run.
    fn work_overdue(&self, i: usize) -> (r: bool)
        requires
            i < self.work.len(),
        ensures
            r == semantics::is_overdue(*self.m, self@, i as int),
    {
        let w = &self.work[i];
        let now = self.now;
        let due = match w.due {
            Some(d) => d <= now,
            None => false,
        };
        w.must && w.after <= now && due && !self.m.internal(&w.req, &self.state, now).is_empty()
    }

    pub(crate) fn overdue(&self) -> (r: bool)
        ensures
            r == semantics::overdue(*self.m, self@),
    {
        for i in 0..self.work.len()
            invariant
                forall|k: int| 0 <= k < i ==> !semantics::is_overdue(*self.m, self@, k),
        {
            if self.work_overdue(i) {
                return true;
            }
        }
        false
    }

    /// Whether work `i` may run: nothing is overdue, or `i` is overdue with the
    /// earliest deadline.
    fn may_run(&self, i: usize) -> (r: bool)
        requires
            i < self.work.len(),
        ensures
            r == (!semantics::overdue(*self.m, self@) || semantics::is_first(*self.m, self@, i as int)),
    {
        if !self.overdue() {
            return true;
        }
        if !self.work_overdue(i) {
            return false;
        }
        for v in 0..self.work.len()
            invariant
                i < self.work.len(),
                forall|k: int| 0 <= k < v && #[trigger] semantics::is_overdue(*self.m, self@, k)
                    ==> semantics::due_le(self@.work[i as int], self@.work[k]),
        {
            if self.work_overdue(v) && !due_le(&self.work[i], &self.work[v]) {
                return false;
            }
        }
        true
    }

    /// Starts work on the clock as it reads now.
    fn start(&mut self, work: Vec<Sched<M::Internal>>)
        ensures
            final(self)@ == (semantics::Config {
                work: semantics::start_all(old(self)@.work, work@, old(self)@.now),
                ..old(self)@
            }),
            final(self).m == old(self).m,
    {
        let now = self.now;
        let ghost (was, all) = (self.work@, work@);
        let mut work = work;
        while !work.is_empty()
            invariant
                self.m == old(self).m,
                now == old(self)@.now,
                work@.len() <= all.len(),
                work@ == all.subrange(all.len() - work@.len(), all.len() as int),
                self@ == (semantics::Config {
                    work: was + all.subrange(0, all.len() - work@.len()).map_values(
                        |s: Sched<M::Internal>| semantics::schedule(now, s),
                    ),
                    ..old(self)@
                }),
            decreases work.len(),
        {
            self.work.push(schedule(now, work.remove(0)));
            proof {
                assert(work@ =~= all.subrange(all.len() - work@.len(), all.len() as int));
                assert(self.work@ =~= was + all.subrange(0, all.len() - work@.len()).map_values(
                    |s: Sched<M::Internal>| semantics::schedule(now, s),
                ));
            }
        }
        proof {
            assert(self.work@ =~= semantics::start_all(was, all, now));
        }
    }

    /// The first copy of `msg` sent and not yet received: any copy would do,
    /// they are equal.
    #[allow(clippy::manual_find)] // a loop, for Verus
    fn first_sent(&self, msg: &M::Dispatch) -> (r: Option<usize>)
        ensures
            r matches Some(i) ==> i < self.sent.len() && self@.sent[i as int] == *msg,
    {
        for i in 0..self.sent.len() {
            if same(&self.sent[i], msg) {
                return Some(i);
            }
        }
        None
    }

    /// An observed step: the event happens here. `Err(())`: the system can't
    /// show this event now.
    pub(crate) fn observe(&mut self, e: &EventOf<M>) -> (r: Result<(), ()>)
        ensures
            r is Ok ==> semantics::step(*old(self).m, old(self)@, Label::Obs(*e), final(self)@),
            final(self).m == old(self).m,
    {
        if self.overdue() {
            return Err(());
        }
        match e {
            Event::Invoke { call, req } => {
                if self.calls.contains_key(call) {
                    return Err(());
                }
                self.calls.insert(*call, Call::InFlight(copy(req)));
                proof {
                    assert(semantics::invoke(*self.m, old(self)@, Label::Obs(*e), self@));
                }
            }
            Event::Return { call, res } => {
                let Some(Call::Done(expected)) = self.calls.get(call) else { return Err(()) };
                if !same(expected, res) {
                    return Err(());
                }
                self.calls.remove(call);
                proof {
                    assert(semantics::ret(*self.m, old(self)@, Label::Obs(*e), self@));
                }
            }
            Event::Receive { msg } => {
                let Some(i) = self.first_sent(msg) else { return Err(()) };
                self.sent.remove(i);
                proof {
                    assert(old(self)@.sent[i as int] == *msg);
                    assert(semantics::receive(*self.m, old(self)@, Label::Obs(*e), self@));
                }
            }
            Event::Clock { at } => {
                if *at < self.now {
                    return Err(());
                }
                self.now = *at;
                proof {
                    assert(semantics::tick(*self.m, old(self)@, Label::Obs(*e), self@));
                }
            }
        }
        Ok(())
    }

    /// A silent step. `Err(())`: the system can't take it now.
    pub(crate) fn silent(&mut self, s: Silent) -> (r: Result<(), ()>)
        ensures
            r is Ok ==> semantics::step(*old(self).m, old(self)@, Label::Silent, final(self)@),
            final(self).m == old(self).m,
    {
        match s {
            Silent::Effect { call, j } => {
                let Some(Call::InFlight(req)) = self.calls.get(&call) else { return Err(()) };
                let mut outs = self.m.external(req, &self.state, self.now);
                if j >= outs.len() || self.overdue() {
                    return Err(());
                }
                let o = outs.swap_remove(j);
                let mut send = o.send;
                self.state = o.next;
                self.calls.insert(call, Call::Done(o.resp));
                self.start(o.work);
                self.sent.append(&mut send);
                proof {
                    proof::effect_step(*self.m, old(self)@, self@, call, j as int);
                }
            }
            Silent::Run { i, j } => {
                if i >= self.work.len() {
                    return Err(());
                }
                let w = &self.work[i];
                let mut outs = self.m.internal(&w.req, &self.state, self.now);
                if j >= outs.len() || w.after > self.now || !self.may_run(i) {
                    return Err(());
                }
                let o = outs.swap_remove(j);
                let mut send = o.send;
                self.work.remove(i);
                self.state = o.next;
                self.start(o.work);
                self.sent.append(&mut send);
                proof {
                    proof::run_step(*self.m, old(self)@, self@, i as int, j as int);
                }
            }
        }
        Ok(())
    }
}

} // verus!

// ------------------------------------------------------------------------
// Not part of `certify`: helpers built on it, for the simulator and coverage.
// Plain Rust, outside Verus.

/// A step the system can take next, other than a new request.
#[derive(Clone, Debug)]
pub(crate) enum Next<M: Model> {
    Silent(Silent),
    /// A response or dispatch delivered to a client.
    Deliver(EventOf<M>),
}

impl<X: Clone, R: Clone> Clone for Call<X, R> {
    fn clone(&self) -> Self {
        match self {
            Call::InFlight(x) => Call::InFlight(x.clone()),
            Call::Done(r) => Call::Done(r.clone()),
        }
    }
}

impl<M: Model> Clone for Config<'_, M> {
    fn clone(&self) -> Self {
        Config { m: self.m, state: self.state.clone(), calls: self.calls.clone(), work: self.work.clone(), sent: self.sent.clone(), now: self.now }
    }
}

impl<M: Model> Config<'_, M> {
    pub(crate) fn state(&self) -> &M::State {
        &self.state
    }

    pub(crate) fn now(&self) -> Time {
        self.now
    }

    /// Calls in flight or answered and not yet returned.
    pub(crate) fn open_calls(&self) -> usize {
        self.calls.len()
    }

    /// Every step that could come next except a new request; [`Config::take`]
    /// decides which are legal.
    pub(crate) fn candidates(&self) -> Vec<Next<M>> {
        let mut out = Vec::new();
        let mut calls: Vec<_> = self.calls.iter().collect();
        calls.sort_by_key(|(c, _)| **c);
        for (call, c) in calls {
            match c {
                Call::InFlight(req) => {
                    let n = self.m.external(req, &self.state, self.now).len();
                    out.extend((0..n).map(|j| Next::Silent(Silent::Effect { call: *call, j })));
                }
                Call::Done(res) => out.push(Next::Deliver(Event::Return { call: *call, res: res.clone() })),
            }
        }
        for (i, w) in self.work.iter().enumerate() {
            let n = self.m.internal(&w.req, &self.state, self.now).len();
            out.extend((0..n).map(|j| Next::Silent(Silent::Run { i, j })));
        }
        out.extend(self.sent.iter().map(|msg| Next::Deliver(Event::Receive { msg: msg.clone() })));
        out
    }

    pub(crate) fn take(&mut self, next: &Next<M>) -> Result<(), ()> {
        match next {
            Next::Silent(s) => self.silent(*s),
            Next::Deliver(e) => self.observe(e),
        }
    }

    pub(crate) fn legal(&self, next: &Next<M>) -> bool {
        self.clone().take(next).is_ok()
    }

    /// The marks on the outcome a silent step takes, in the configuration it
    /// is taken from.
    fn marks_of(&self, s: Silent) -> Vec<&'static str> {
        match s {
            Silent::Effect { call, j } => match self.calls.get(&call) {
                Some(Call::InFlight(req)) => self.m.external(req, &self.state, self.now).get(j).map(|o| o.marks.clone()).unwrap_or_default(),
                _ => Vec::new(),
            },
            Silent::Run { i, j } => match self.work.get(i) {
                Some(w) => self.m.internal(&w.req, &self.state, self.now).get(j).map(|o| o.marks.clone()).unwrap_or_default(),
                None => Vec::new(),
            },
        }
    }
}

/// The marks on the outcomes the execution a certificate describes takes:
/// coverage, from one concrete explanation of a trace. `Err(k)` as for
/// [`certify`].
pub fn marks<M: Model>(
    m: &M,
    init: M::State,
    trace: &[EventOf<M>],
    cert: &[Vec<Silent>],
) -> Result<BTreeSet<&'static str>, usize> {
    let mut c = Config::initial(m, init);
    let mut seen = BTreeSet::new();
    for (k, e) in trace.iter().enumerate() {
        let Some(silent) = cert.get(k) else { return Err(k) };
        for s in silent {
            seen.extend(c.marks_of(*s));
            c.silent(*s).map_err(|()| k)?;
        }
        c.observe(e).map_err(|()| k)?;
    }
    Ok(seen)
}
