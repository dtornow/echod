//! A model run as a server: it takes requests and answers them, choosing at
//! random among everything the model allows: which outcome a request takes
//! effect with, when internal work runs, when responses and dispatches are
//! delivered. Overdue work runs before anything else.
//!
//! Every move goes through the same replay `certify` uses, so the simulator
//! can't do anything the model doesn't allow. Run a different model (one with a
//! bug planted) to give a fuzz driver a server to catch.

use crate::certificate::{Config, EventOf, Next, Silent};
use crate::{CallId, Model};

pub struct Sim<'m, M: Model> {
    c: Config<'m, M>,
    /// Chooses among `n` alternatives: a seeded generator, or a testing
    /// library that records the choices so it can replay and shrink them.
    pick: Box<dyn FnMut(usize) -> usize + 'm>,
}

impl<'m, M: Model> Sim<'m, M> {
    /// Choices from a generator seeded with `seed`.
    pub fn new(m: &'m M, init: M::State, seed: u64) -> Self {
        let mut rng = seed | 1;
        Self::with_choices(m, init, move |n| {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            (rng % n as u64) as usize
        })
    }

    /// Choices from `pick(n)`, which must return a number below `n`.
    pub fn with_choices(m: &'m M, init: M::State, pick: impl FnMut(usize) -> usize + 'm) -> Self {
        Sim { c: Config::initial(m, init), pick: Box::new(pick) }
    }

    /// The server's state.
    pub fn state(&self) -> &M::State {
        self.c.state()
    }

    /// Calls sent and not yet answered.
    pub fn open_calls(&self) -> usize {
        self.c.open_calls()
    }

    fn next(&mut self, n: usize) -> usize {
        let k = (self.pick)(n);
        assert!(k < n, "a choice among {n} must be below {n}, not {k}");
        k
    }

    fn legal(&self) -> Vec<Next<M>> {
        self.c.candidates().into_iter().filter(|mv| self.c.legal(mv)).collect()
    }

    /// Runs work until nothing is overdue.
    fn catch_up(&mut self) {
        while self.c.overdue() {
            let runs: Vec<_> = self.legal().into_iter().filter(|n| matches!(n, Next::Silent(Silent::Run { .. }))).collect();
            if runs.is_empty() {
                return;
            }
            let k = self.next(runs.len());
            self.c.take(&runs[k]).expect("legal");
        }
    }

    /// A client sends a request. Overdue work runs first.
    pub fn invoke(&mut self, call: CallId, req: M::External) -> EventOf<M> {
        self.catch_up();
        let e = crate::Event::Invoke { call, req };
        self.c.observe(&e).expect("a fresh call id");
        e
    }

    /// One thing the server does next, at random: a call takes effect, work
    /// runs, or a response or dispatch is delivered. `Some(event)` if a client
    /// observes it; `None` if it was silent or nothing could happen.
    pub fn step(&mut self) -> Option<EventOf<M>> {
        let moves = self.legal();
        if moves.is_empty() {
            return None;
        }
        let k = self.next(moves.len());
        self.c.take(&moves[k]).expect("legal");
        match &moves[k] {
            Next::Deliver(e) => Some(e.clone()),
            Next::Silent(_) => None,
        }
    }

    /// Steps until every call has been answered; the events clients observe.
    /// Bounded, in case the model allows a call to never take effect.
    pub fn settle(&mut self) -> Vec<EventOf<M>> {
        let mut out = Vec::new();
        for _ in 0..10_000 {
            if self.open_calls() == 0 {
                break;
            }
            out.extend(self.step());
        }
        out
    }
}
