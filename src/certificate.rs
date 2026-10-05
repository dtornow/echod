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
    /// Time passes. Silent.
    Advance { to: Time },
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
    now: Time,
    calls: HashMap<CallId, Call<M::External, M::Response>>,
    pub work: Vec<Work<M::Internal>>,
    pub sent: Vec<M::Dispatch>,
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
        Config { m, state: init, now: 0, calls: HashMap::new(), work: Vec::new(), sent: Vec::new() }
    }

    fn work_overdue(&self, w: &Work<M::Internal>) -> bool {
        w.must
            && w.after <= self.now
            && w.due.is_some_and(|d| d <= self.now)
            && !self.m.internal(&w.req, &self.state, self.now).is_empty()
    }

    fn overdue(&self) -> bool {
        self.work.iter().any(|w| self.work_overdue(w))
    }

    fn can_advance(&self, t: Time) -> bool {
        self.now < t
            && self.work.iter().all(|w| {
                !w.must
                    || match w.due {
                        None => true,
                        Some(d) => t <= d || (d <= self.now && self.m.internal(&w.req, &self.state, self.now).is_empty()),
                    }
            })
    }

    fn start(&mut self, spawn: Vec<Sched<M::Internal>>) -> Option<()> {
        for s in spawn {
            self.work.push(schedule(self.now, s)?);
        }
        Some(())
    }

    /// One move: the event it shows a client, if any. `Err(())`: the system
    /// can't make this move here.
    pub fn apply(&mut self, mv: MoveOf<M>) -> Result<Option<EventOf<M>>, ()> {
        let now = self.now;
        match mv {
            Move::Invoke { call, req } => {
                if self.calls.contains_key(&call) || self.overdue() {
                    return Err(());
                }
                self.calls.insert(call, Call::InFlight(req.clone()));
                Ok(Some(Event::Invoke { at: now, call, req }))
            }
            Move::Return { call, res } => {
                let Some(Call::Done(expected)) = self.calls.get(&call) else { return Err(()) };
                if !self.m.admits(expected, &res) || self.overdue() {
                    return Err(());
                }
                self.calls.remove(&call);
                Ok(Some(Event::Return { at: now, call, res }))
            }
            Move::Receive { i } => {
                if i >= self.sent.len() || self.overdue() {
                    return Err(());
                }
                let msg = self.sent.remove(i);
                Ok(Some(Event::Receive { at: now, msg }))
            }
            Move::Effect { call, j } => {
                let Some(Call::InFlight(req)) = self.calls.get(&call) else { return Err(()) };
                let mut outs = self.m.external(req, &self.state, now);
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
                let mut outs = self.m.internal(&w.req, &self.state, now);
                if j >= outs.len() || w.after > now || (self.overdue() && !self.work_overdue(w)) {
                    return Err(());
                }
                let o = outs.swap_remove(j);
                self.work.remove(i);
                self.state = o.next;
                self.start(o.spawn).ok_or(())?;
                self.sent.extend(o.send);
                Ok(None)
            }
            Move::Advance { to } => {
                if !self.can_advance(to) {
                    return Err(());
                }
                self.now = to;
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
