//! Certificates: checking an execution someone found.
//!
//! Finding an execution is hard: the checker searches. Checking one is easy:
//! walk it, one step at a time. A certificate is the list of moves the checker
//! found; [`certify`] rebuilds the configurations, fails on the first move the
//! system can't make, and returns what the execution shows a client.
//!
//! This file is the Rust copy of `replay` and `certify` in `lean/Accordant.lean`,
//! where `certify m init moves = some trace` is proved to imply that the trace is
//! valid. Keep the two in step: the soundness of the checker rests on this file
//! alone, not on the search.

use std::collections::HashMap;

use crate::checker::Event;
use crate::{CallId, Model, Sched, Time};

/// One move of an execution, as the checker reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Move<X, R> {
    /// A client sends a request. Observed.
    Invoke { call: CallId, req: X },
    /// A client receives the response to its call. Observed.
    Return { call: CallId, res: R },
    /// A client receives the `i`-th dispatch sent and not yet received. Observed.
    Receive { i: usize },
    /// The call takes effect with the `j`-th of its outcomes. Silent.
    Effect { call: CallId, j: usize },
    /// The `i`-th pending work runs with the `j`-th of its outcomes. Silent.
    Run { i: usize, j: usize },
}

pub type MoveOf<M> = Move<<M as Model>::External, <M as Model>::Response>;
pub type EventOf<M> = Event<<M as Model>::External, <M as Model>::Response, <M as Model>::Dispatch>;

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

/// `None`: the time overflows, which the model's unbounded clock never does.
fn schedule<I>(now: Time, s: Sched<I>) -> Option<Work<I>> {
    Some(match s {
        Sched::Later(req) => Work { req, after: now, due: None, must: true },
        Sched::Timer(t, req) => Work { req, after: t.max(now), due: Some(t.max(now)), must: true },
        Sched::After(t, req) => Work { req, after: t.max(now), due: None, must: true },
        Sched::Within(d, req) => Work { req, after: now, due: Some(now.checked_add(d)?), must: true },
        Sched::Maybe(req) => Work { req, after: now, due: None, must: false },
    })
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

    fn overdue(&self) -> bool {
        self.work.iter().any(|w| self.work_overdue(w))
    }

    /// Whether `w` may run: nothing is overdue, or `w` is overdue with the
    /// earliest deadline.
    fn may_run(&self, w: &Work<M::Internal>) -> bool {
        !self.overdue() || (self.work_overdue(w) && self.work.iter().all(|v| !self.work_overdue(v) || due_le(w, v)))
    }

    /// Starts work on the clock of the state the step led to.
    fn start(&mut self, spawn: Vec<Sched<M::Internal>>) -> Option<()> {
        let now = self.m.now(&self.state);
        for s in spawn {
            self.work.push(schedule(now, s)?);
        }
        Some(())
    }

    /// One move: the event it shows a client, if any. `Err(())`: the system
    /// can't make this move here.
    pub fn apply(&mut self, mv: MoveOf<M>) -> Result<Option<EventOf<M>>, ()> {
        match mv {
            Move::Invoke { call, req } => {
                if self.calls.contains_key(&call) || self.overdue() {
                    return Err(());
                }
                self.calls.insert(call, Call::InFlight(req.clone()));
                Ok(Some(Event::Invoke { call, req }))
            }
            Move::Return { call, res } => {
                let Some(Call::Done(expected)) = self.calls.get(&call) else { return Err(()) };
                if !self.m.admits(expected, &res) || self.overdue() {
                    return Err(());
                }
                self.calls.remove(&call);
                Ok(Some(Event::Return { call, res }))
            }
            Move::Receive { i } => {
                if i >= self.sent.len() || self.overdue() {
                    return Err(());
                }
                let msg = self.sent.remove(i);
                Ok(Some(Event::Receive { msg }))
            }
            Move::Effect { call, j } => {
                let Some(Call::InFlight(req)) = self.calls.get(&call) else { return Err(()) };
                let mut outs = self.m.external(req, &self.state);
                if j >= outs.len() || self.overdue() {
                    return Err(());
                }
                let o = outs.swap_remove(j);
                self.state = o.next;
                self.calls.insert(call, Call::Done(o.res));
                self.start(o.spawn).ok_or(())?;
                self.sent.extend(o.send);
                Ok(None)
            }
            Move::Run { i, j } => {
                let Some(w) = self.work.get(i) else { return Err(()) };
                let mut outs = self.m.internal(&w.req, &self.state);
                if j >= outs.len() || w.after > self.m.now(&self.state) || !self.may_run(w) {
                    return Err(());
                }
                let o = outs.swap_remove(j);
                self.work.remove(i);
                self.state = o.next;
                self.start(o.spawn).ok_or(())?;
                self.sent.extend(o.send);
                Ok(None)
            }
        }
    }
}

/// What a certificate shows a client, if every move in it is legal; otherwise
/// the position of the first illegal move.
pub fn certify<M: Model>(m: &M, init: M::State, moves: impl IntoIterator<Item = MoveOf<M>>) -> Result<Vec<EventOf<M>>, usize> {
    let mut c = Config::initial(m, init);
    let mut shown = Vec::new();
    for (k, mv) in moves.into_iter().enumerate() {
        shown.extend(c.apply(mv).map_err(|()| k)?);
    }
    Ok(shown)
}
