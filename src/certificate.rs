//! Certificates: checking an execution someone found.
//!
//! Finding an execution is hard: the checker searches. Checking one is easy:
//! walk it, one step at a time. The trace already has the observed steps; a
//! certificate adds the silent ones the checker found: for each event, which
//! calls took effect and which work ran just before it, with which outcomes.
//! [`certify`] rebuilds the configurations and fails on the first step the
//! system can't make.
//!
//! This file is the Rust copy of `replay` and `certify` in `lean/Accordant.lean`,
//! where an accepted certificate is proved to make the trace valid. Keep the two
//! in step: the soundness of the checker rests on this file alone, not on the
//! search.

use std::collections::{BTreeSet, HashMap};

use crate::checker::Event;
use crate::{CallId, Model, Sched, Time};

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
pub fn certify<M: Model>(m: &M, init: M::State, trace: &[EventOf<M>], cert: &[Vec<Silent>]) -> Result<(), usize> {
    let mut c = Config::initial(m, init);
    for (k, e) in trace.iter().enumerate() {
        let Some(silent) = cert.get(k) else { return Err(k) };
        for s in silent {
            c.silent(*s).map_err(|()| k)?;
        }
        c.observe(e).map_err(|()| k)?;
    }
    Ok(())
}

enum Call<X, R> {
    InFlight(X),
    Done(R),
}

/// Internal work started and not yet run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Work<I> {
    pub req: I,
    pub after: Time,
    pub due: Option<Time>,
    pub must: bool,
}

/// Everything about the system at one point, seen or not.
pub(crate) struct Config<'m, M: Model> {
    m: &'m M,
    state: M::State,
    calls: HashMap<CallId, Call<M::External, M::Response>>,
    pub work: Vec<Work<M::Internal>>,
    pub sent: Vec<M::Dispatch>,
}

fn due_le<I>(w: &Work<I>, v: &Work<I>) -> bool {
    match (w.due, v.due) {
        (Some(d), Some(e)) => d <= e,
        _ => false,
    }
}

fn schedule<I>(now: Time, s: Sched<I>) -> Work<I> {
    match s {
        Sched::Later(req) => Work { req, after: now, due: None, must: true },
        Sched::Timer(t, req) => Work { req, after: t.max(now), due: Some(t.max(now)), must: true },
    }
}

impl<'m, M: Model> Config<'m, M> {
    pub fn initial(m: &'m M, init: M::State) -> Self {
        Config { m, state: init, calls: HashMap::new(), work: Vec::new(), sent: Vec::new() }
    }

    /// Work whose deadline has come on the model's clock and that can run.
    fn work_overdue(&self, w: &Work<M::Internal>) -> bool {
        let now = self.m.now(&self.state);
        w.must && w.after <= now && w.due.is_some_and(|d| d <= now) && !self.m.internal(&w.req, &self.state).is_empty()
    }

    pub(crate) fn overdue(&self) -> bool {
        self.work.iter().any(|w| self.work_overdue(w))
    }

    /// Whether `w` may run: nothing is overdue, or `w` is overdue with the
    /// earliest deadline.
    fn may_run(&self, w: &Work<M::Internal>) -> bool {
        !self.overdue() || (self.work_overdue(w) && self.work.iter().all(|v| !self.work_overdue(v) || due_le(w, v)))
    }

    /// Starts work on the clock of the state the step led to.
    fn start(&mut self, work: Vec<Sched<M::Internal>>) {
        let now = self.m.now(&self.state);
        self.work.extend(work.into_iter().map(|s| schedule(now, s)));
    }

    /// An observed step: the event happens here. `Err(())`: the system can't
    /// show this event now.
    pub fn observe(&mut self, e: &EventOf<M>) -> Result<(), ()> {
        if self.overdue() {
            return Err(());
        }
        match e {
            Event::Invoke { call, req } => {
                if self.calls.contains_key(call) {
                    return Err(());
                }
                self.calls.insert(*call, Call::InFlight(req.clone()));
            }
            Event::Return { call, res } => {
                let Some(Call::Done(expected)) = self.calls.get(call) else { return Err(()) };
                if expected != res {
                    return Err(());
                }
                self.calls.remove(call);
            }
            Event::Receive { msg } => {
                // The first copy sent: any copy would do, they are equal.
                let Some(i) = self.sent.iter().position(|m| m == msg) else { return Err(()) };
                self.sent.remove(i);
            }
        }
        Ok(())
    }

    /// A silent step. `Err(())`: the system can't take it now.
    pub fn silent(&mut self, s: Silent) -> Result<(), ()> {
        match s {
            Silent::Effect { call, j } => {
                let Some(Call::InFlight(req)) = self.calls.get(&call) else { return Err(()) };
                let mut outs = self.m.external(req, &self.state);
                if j >= outs.len() || self.overdue() {
                    return Err(());
                }
                let o = outs.swap_remove(j);
                self.state = o.next;
                self.calls.insert(call, Call::Done(o.resp));
                self.start(o.work);
                self.sent.extend(o.send);
            }
            Silent::Run { i, j } => {
                let Some(w) = self.work.get(i) else { return Err(()) };
                let mut outs = self.m.internal(&w.req, &self.state);
                if j >= outs.len() || w.after > self.m.now(&self.state) || !self.may_run(w) {
                    return Err(());
                }
                let o = outs.swap_remove(j);
                self.work.remove(i);
                self.state = o.next;
                self.start(o.work);
                self.sent.extend(o.send);
            }
        }
        Ok(())
    }
}

// ------------------------------------------------------------------------
// Not part of `certify`: helpers built on it, for the simulator and coverage.

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
        Config { m: self.m, state: self.state.clone(), calls: self.calls.clone(), work: self.work.clone(), sent: self.sent.clone() }
    }
}

impl<M: Model> Config<'_, M> {
    pub(crate) fn state(&self) -> &M::State {
        &self.state
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
                    let n = self.m.external(req, &self.state).len();
                    out.extend((0..n).map(|j| Next::Silent(Silent::Effect { call: *call, j })));
                }
                Call::Done(res) => out.push(Next::Deliver(Event::Return { call: *call, res: res.clone() })),
            }
        }
        for (i, w) in self.work.iter().enumerate() {
            let n = self.m.internal(&w.req, &self.state).len();
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

    /// The marks of a silent step, in the configuration it is taken from.
    fn marks_of(&self, s: Silent) -> Vec<&'static str>
    where
        M: crate::Marks,
    {
        match s {
            Silent::Effect { call, j } => match self.calls.get(&call) {
                Some(Call::InFlight(req)) => {
                    let outs = self.m.external(req, &self.state);
                    outs.get(j).map(|o| self.m.external_marks(req, &self.state, o)).unwrap_or_default()
                }
                _ => Vec::new(),
            },
            Silent::Run { i, j } => match self.work.get(i) {
                Some(w) => {
                    let outs = self.m.internal(&w.req, &self.state);
                    outs.get(j).map(|o| self.m.internal_marks(&w.req, &self.state, o)).unwrap_or_default()
                }
                None => Vec::new(),
            },
        }
    }
}

/// The marks the execution a certificate describes passes through: coverage,
/// from one concrete explanation of a trace. `Err(k)` as for [`certify`].
pub fn marks<M: crate::Marks>(
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
