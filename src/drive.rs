//! Driving a model: send it requests, let it run, and record what happens.
//!
//! The model runs as a server ([`Sim`]). A run is a sequence of decisions:
//! send a request now or let the system move, which request, which of the
//! moves the system can make. Every decision is a choice among `n`
//! alternatives, taken from [`Choices`], which records it. The result is the
//! trace (what was sent and what came back) and the choices that produced it;
//! replaying the choices reproduces the trace.
//!
//! The model says which requests to send ([`Explore`]); nothing here knows
//! anything about a particular model.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::certificate::EventOf;
use crate::{Action, CallId, Explore, Sim};

/// One decision: the `k`-th of `n` alternatives.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Choice {
    pub n: usize,
    pub k: usize,
}

/// How often each labeled alternative was taken, across runs that share it.
/// With it, a random choice among labeled alternatives takes one of the least
/// taken labels: rare behaviors get their turn.
#[derive(Clone, Debug, Default)]
pub struct Tried(Rc<RefCell<HashMap<&'static str, usize>>>);

impl Tried {
    pub fn count(&self, label: &str) -> usize {
        self.0.borrow().get(label).copied().unwrap_or(0)
    }
}

/// Where a run's decisions come from: a prefix to replay, then a seeded
/// generator (or, with no generator, the first alternative). Every decision
/// taken is recorded, as its index, so a replay needs nothing else.
#[derive(Clone, Debug)]
pub struct Choices {
    prefix: Vec<usize>,
    rng: Option<u64>,
    tried: Option<Tried>,
    recorded: Vec<Choice>,
}

impl Choices {
    /// Random decisions, from a generator seeded with `seed`.
    pub fn random(seed: u64) -> Self {
        Choices { prefix: Vec::new(), rng: Some(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1), tried: None, recorded: Vec::new() }
    }

    /// Random choices among labeled alternatives take a least-taken label,
    /// counted in `tried` (shared across runs).
    pub fn learning(mut self, tried: &Tried) -> Self {
        self.tried = Some(tried.clone());
        self
    }

    /// The decisions of a recorded run, in order. A recorded `k` that doesn't
    /// fit (`k >= n`, after the recording was edited) becomes 0; past the end
    /// of the recording, every decision is 0, the first alternative.
    pub fn replay(recorded: &[Choice]) -> Self {
        Choices { prefix: recorded.iter().map(|c| c.k).collect(), rng: None, tried: None, recorded: Vec::new() }
    }

    /// A number below `n`. A choice among one alternative is no choice: it is
    /// 0, and not recorded.
    pub fn pick(&mut self, n: usize) -> usize {
        assert!(n > 0, "a choice among no alternatives");
        if n == 1 {
            return 0;
        }
        let k = match self.replayed(n) {
            Some(k) => k,
            None => self.draw(n).unwrap_or(0),
        };
        self.recorded.push(Choice { n, k });
        k
    }

    /// The index of one of `labels`. Random, it takes one of the labels taken
    /// least so far (with [`Choices::learning`]); replayed, the recorded index.
    pub fn pick_labeled(&mut self, labels: &[&'static str]) -> usize {
        let n = labels.len();
        assert!(n > 0, "a choice among no alternatives");
        let k = if n == 1 {
            0
        } else {
            let k = match (self.replayed(n), self.tried.clone()) {
                (Some(k), _) => k,
                (None, Some(tried)) if self.rng.is_some() => {
                    let least = labels.iter().map(|l| tried.count(l)).min().expect("not empty");
                    let fewest: Vec<usize> = (0..n).filter(|&i| tried.count(labels[i]) == least).collect();
                    fewest[self.draw(fewest.len()).expect("random")]
                }
                (None, _) => self.draw(n).unwrap_or(0),
            };
            self.recorded.push(Choice { n, k });
            k
        };
        if let Some(tried) = &self.tried {
            *tried.0.borrow_mut().entry(labels[k]).or_default() += 1;
        }
        k
    }

    fn replayed(&self, n: usize) -> Option<usize> {
        self.prefix.get(self.recorded.len()).map(|&k| if k < n { k } else { 0 })
    }

    fn draw(&mut self, n: usize) -> Option<usize> {
        let r = self.rng.as_mut()?;
        *r ^= *r << 13;
        *r ^= *r >> 7;
        *r ^= *r << 17;
        Some((*r % n as u64) as usize)
    }

    /// The decisions taken so far.
    pub fn recorded(&self) -> &[Choice] {
        &self.recorded
    }
}

/// How a run goes.
#[derive(Clone, Debug)]
pub struct Drive {
    /// Actions to take (requests to send, clock moves), besides the ones
    /// [`Explore::finish`] adds.
    pub requests: usize,
    /// At most this many calls in flight at once.
    pub concurrency: usize,
    /// Take most requests from [`Explore::suggest`] rather than
    /// [`Explore::arbitrary`].
    pub guided: bool,
}

impl Default for Drive {
    fn default() -> Self {
        Drive { requests: 30, concurrency: 3, guided: true }
    }
}

/// A run: what clients saw, and the decisions that produced it.
pub struct Run<M: Explore> {
    pub trace: Vec<EventOf<M>>,
    pub choices: Vec<Choice>,
}

/// Drives `model` from `init`: sends requests, moves the clock and lets the
/// system move, every decision from `choices`, until the actions are taken and
/// every call answered; then takes [`Explore::finish`]'s actions one at a
/// time, each settled before the next. Returns what clients saw and the
/// decisions taken.
pub fn drive<M: Explore>(model: &M, init: M::State, cfg: &Drive, choices: Choices) -> Run<M> {
    let choices = RefCell::new(choices);
    let pick = |n: usize| choices.borrow_mut().pick(n);
    let pick_labeled = |labels: &[&'static str]| choices.borrow_mut().pick_labeled(labels);
    let mut sim = Sim::with_choices(model, init, pick);
    let mut trace = Vec::new();
    let mut call: CallId = 0;
    let mut sent = 0;
    // The system can always make a move while a call is open, so this ends.
    while sent < cfg.requests || sim.open_calls() > 0 {
        let act = sent < cfg.requests && sim.open_calls() < cfg.concurrency.max(1) && pick(2) == 0;
        if act {
            let a = action(model, sim.state(), sim.now(), cfg.guided, &pick, &pick_labeled);
            sent += 1;
            trace.push(take(&mut sim, &mut call, a));
        } else if let Some(e) = sim.step() {
            trace.push(e);
        } else if sent >= cfg.requests {
            break;
        }
    }
    let mut last = model.finish(sim.state(), sim.now());
    last.reverse();
    while let Some(a) = last.pop() {
        trace.push(take(&mut sim, &mut call, a));
        trace.extend(sim.settle());
    }
    drop(sim);
    Run { trace, choices: choices.into_inner().recorded }
}

fn take<M: Explore>(sim: &mut Sim<'_, M>, call: &mut CallId, a: Action<M::External>) -> EventOf<M> {
    match a {
        Action::Request(req) => {
            *call += 1;
            sim.invoke(*call, req)
        }
        Action::Clock(at) => sim.clock(at),
    }
}

fn action<M: Explore>(
    model: &M,
    state: &M::State,
    now: crate::Time,
    guided: bool,
    pick: &impl Fn(usize) -> usize,
    pick_labeled: &impl Fn(&[&'static str]) -> usize,
) -> Action<M::External> {
    if guided {
        let suggestions = model.suggest(state, now);
        if !suggestions.is_empty() && pick(4) != 0 {
            let labels: Vec<&'static str> = suggestions.iter().map(|(_, why)| *why).collect();
            return suggestions[pick_labeled(&labels)].0.clone();
        }
    }
    model.arbitrary(state, now, &mut |n| pick(n))
}
