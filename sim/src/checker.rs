//! Linearizability of a history against the model, per origin.
//!
//! Every operation the protocol admits is single-origin, so an origin's
//! operations are a history of their own and are checked alone, with the
//! sweeps among them. The search (Wing & Gong, with Lowe's memoisation) asks:
//! is there an order of these operations, each placed between its invocation
//! and its return, such that the model gives every answer the client saw —
//! and that ends in the rows the bucket holds? Both at once, since two orders
//! can explain the same answers and leave different state.
//!
//! An entry without an outcome — a sweep whose commit was reported failed, a
//! request the run ended on — may have taken effect or not, so the search
//! tries it both ways: placed, or skipped.

use std::collections::HashSet;

use echod_kernel as k;
use serde_json::Value;

use crate::history::Entry;
use crate::model;

#[derive(Debug)]
pub enum Verdict {
    Linearizable { steps: u64 },
    NotLinearizable { origin: String, steps: u64, detail: String },
    Undecided { origin: String, steps: u64 },
}

/// Check one document's entries against `final_state`, the document at the
/// end of the run: an origin's objects, or a schedule's row. `budget`
/// bounds the search.
pub fn check_origin(origin: &str, entries: &[Entry], final_state: &k::State, cfg: &k::Config, budget: u64) -> Verdict {
    let n = entries.len();
    let want_final = model::canon_state(final_state);
    // Frames of the depth-first search: the state, and which entries are
    // linearised so far.
    struct Frame {
        stamp: u64,
        state: k::State,
        done: Bits,
        next: usize,
    }
    let mut seen: HashSet<(Bits, u64)> = HashSet::new();
    let mut stack = vec![Frame { stamp: 0, state: model::state(), done: Bits::new(n), next: 0 }];
    let mut steps: u64 = 0;
    let mut last_mismatch = String::new();
    while let Some(frame) = stack.last_mut() {
        if frame.done.count() == n {
            if model::canon_state(&frame.state) == want_final {
                return Verdict::Linearizable { steps };
            }
            last_mismatch = "every answer explained, but the order leaves other rows than the bucket holds".to_string();
            stack.pop();
            continue;
        }
        // The next candidate: not done, and no other undone entry returned
        // before it was invoked. Each candidate is tried placed (even
        // variants) and, if its outcome is unknown, skipped (odd variants).
        let done = frame.done.clone();
        let mut candidate = None;
        for v in frame.next..2 * n {
            let i = v / 2;
            let skip = v % 2 == 1;
            if done.get(i) || (skip && entries[i].outcome.is_some()) {
                continue;
            }
            let blocked = (0..n).any(|j| j != i && !done.get(j) && entries[j].ret < entries[i].invoke);
            if !blocked {
                candidate = Some((i, skip));
                break;
            }
        }
        let Some((i, skip)) = candidate else {
            stack.pop();
            continue;
        };
        frame.next = 2 * i + if skip { 2 } else { 1 };
        steps += 1;
        if steps > budget {
            return Verdict::Undecided { origin: origin.to_string(), steps };
        }
        let mut state = model::clone_state(&frame.state);
        let mut stamp = frame.stamp;
        let e = &entries[i];
        if !skip {
            let got = model::step(&mut state, &mut stamp, &e.op, e.now, cfg, &corr(e));
            if let Some(want) = &e.outcome {
                if !same_answer(want, &got) {
                    last_mismatch = format!("entry {} {} by {} at {}: answered {} {}, model says {} {}", e.id, e.op.kind(), e.client, e.now, want.0, compact(&want.1), got.0, compact(&got.1));
                    continue;
                }
            }
        }
        let mut new_done = done;
        new_done.set(i);
        // The same rows at a different stamp are a different state: the next
        // step is decided no earlier than the stamp.
        let key = (new_done.clone(), hash(&model::canon_state(&state)) ^ stamp.wrapping_mul(0x9e37_79b9_7f4a_7c15));
        if !seen.insert(key) {
            continue;
        }
        stack.push(Frame { stamp, state, done: new_done, next: 0 });
    }
    Verdict::NotLinearizable { origin: origin.to_string(), steps, detail: last_mismatch }
}

/// A set of entry indices.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Self {
        Self(vec![0; n.div_ceil(64).max(1)])
    }
    fn get(&self, i: usize) -> bool {
        self.0[i / 64] & (1u64 << (i % 64)) != 0
    }
    fn set(&mut self, i: usize) {
        self.0[i / 64] |= 1u64 << (i % 64);
    }
    fn count(&self) -> usize {
        self.0.iter().map(|w| w.count_ones() as usize).sum()
    }
}

/// Two answers agree when their statuses do and, for an answer that carries
/// state, the state does. The reason string of an error is the edge's
/// wording, not the model's: a validator in front of the kernel says why.
pub fn same_answer(a: &(u16, Value), b: &(u16, Value)) -> bool {
    a.0 == b.0 && (a.0 >= 400 || a.1 == b.1)
}

/// The correlation id a client used for the entry: the model must render the
/// same inner envelopes.
pub fn corr(e: &Entry) -> String {
    format!("c{}", e.id)
}

fn compact(v: &Value) -> String {
    let s = v.to_string();
    if s.len() > 300 {
        format!("{}…", &s[..300])
    } else {
        s
    }
}

fn hash(v: &Value) -> u64 {
    echod_logic::keys::fnv1a(&v.to_string())
}
