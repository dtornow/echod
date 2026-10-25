//! A run as a trace of the Resonate model, checked by `accordant`.
//!
//! The history becomes the checker's trace: every request a client made is
//! an `Invoke` and, if it was answered, a `Return`; every step a node took
//! is a call of its own, `Request::Step`, at the instant the node decided
//! it; every message the bus carried is a `Receive`; and the clock moves
//! (`Clock`) at every instant something happened. The checker then asks
//! whether some execution of the model shows exactly these observations.
//! The model is partitioned by origin, as the documents are.
//!
//! The model runs with `reported`: a node sweeps a document when it gets to
//! it, and a client may read in between, so the model arms no work of its
//! own and takes each step as the node reports it (`Note::*Begin`,
//! `Note::*End`): a request's own drain after the request (what the request
//! left to do: resumes, unblocks, redispatches), a sweep (everything due:
//! deadlines and leases too), a fire's two halves. A promise past its
//! deadline settles when a request reads it, as the node keeps the reading
//! in its document, or when a sweep gets to it. A step whose write the node
//! did not see land may have landed all the same (a lost acknowledgement, a
//! crash): the store says, by the nonce the write carries, and the step is
//! in the trace or not.
//!
//! Where a call sits. A node decides a request at one instant, the kernel's
//! `now`: `head.debug_time`, the instant the client sent it at, or the
//! document's stamp if that is later; and it reports the instant. The trace
//! puts the call's `Invoke` and `Return` both there, so the model has one
//! place to put it: a run's clients overlap freely, and the checker would
//! otherwise weigh every clock move in every span. Two steps on one
//! document at one instant are ordered by the document's version each made
//! or saw. A call answered without a step (refused at the door) keeps its
//! span, from the instant it was sent to the instant it was answered. The
//! instants are the node's claims, and the check is that the claims,
//! together, are an execution of the model.
//!
//! A step that wrote nothing sits at the stamp of the version it saw, not
//! at its own instant. Its own instant may be later than that of a write it
//! did not see, decided earlier and landed later (a create sent at 1627
//! lands at 1650; a read sent at 1641 saw the document without it), and the
//! model's clock cannot go back to take the write after the read. Nothing
//! on the document was due at the step's instant, else the step's sweep
//! would have written; so the model answers the same at the stamp, where
//! the write has not happened yet either.
//!
//! One clock. The stamp a request is clamped to is an instant some step was
//! decided at, which the trace carries as a clock move. So the run's nodes
//! must keep the one clock too: with skew, drift or jumps a node sweeps at
//! an instant of its own, and the model, whose deadlines are exact, would
//! see a deadline fire early or late.

use std::collections::BTreeMap;

use accordant::{Checker, Config, Event, Grouped, Violation};
use resonate::{dominates, Dispatch, Request, Resonate, Response, Server};

use crate::bus::Sent;
use crate::history::{Entry, StepRec};
use crate::wire::{decode, encode};
use crate::workload::WORKER;

pub type Trace = Vec<Event<Request, Response, Dispatch>>;

/// Call ids for the nodes' steps, past any entry's.
const STEP_CALLS: u64 = 1 << 40;

/// The trace, from what the run recorded: the entries, the steps that
/// landed, the messages.
pub fn trace(entries: &[Entry], steps: &[StepRec], sent: &[Sent]) -> Trace {
    let mut steps: Vec<StepRec> = steps.to_vec();
    // A step that wrote nothing sits at the stamp of the version it saw: the
    // instant of the write that made it (the empty document's is 0).
    let stamps: BTreeMap<(String, u64), u64> = steps.iter().filter(|s| s.wrote).map(|s| ((s.target.clone(), s.seq), s.now)).collect();
    for s in steps.iter_mut() {
        if !s.wrote {
            s.now = stamps.get(&(s.target.clone(), s.seq)).copied().unwrap_or(0);
        }
    }
    // Two steps on one document at one instant, in the order of the
    // versions they made or saw, the write before what saw it: the node
    // reports them as their commits come back, which may be the other way
    // round.
    let mut groups: BTreeMap<(u64, String), Vec<usize>> = BTreeMap::new();
    for (i, s) in steps.iter().enumerate() {
        groups.entry((s.now, s.target.clone())).or_default().push(i);
    }
    for idx in groups.values().filter(|g| g.len() > 1) {
        let mut orders: Vec<u64> = idx.iter().map(|&i| steps[i].order).collect();
        orders.sort_unstable();
        let mut by_seq: Vec<usize> = idx.clone();
        by_seq.sort_by_key(|&i| (steps[i].seq, !steps[i].wrote, steps[i].order));
        for (i, order) in by_seq.into_iter().zip(orders) {
            steps[i].order = order;
        }
    }

    // (instant, slot, rank, id, event): a request at the slot of its step,
    // invoke then return, then the step itself; a message received after
    // everything at its instant; a call without a step first, and its
    // answer last, at theirs. A call without a step and without an answer
    // took no effect: it is left out.
    const FIRST: u64 = 0;
    const LAST: u64 = u64::MAX;
    let mut items: Vec<(u64, u64, u8, u64, Event<Request, Response, Dispatch>)> = Vec::new();
    let mut of_entry: BTreeMap<u64, Vec<&StepRec>> = BTreeMap::new();
    for s in &steps {
        if let Some(e) = s.request {
            of_entry.entry(e).or_default().push(s);
        }
    }
    for e in entries {
        let (from, to) = match (of_entry.get(&e.id), &e.outcome) {
            // a detached create has two steps, on two documents, in either
            // order of instants: the call spans them
            (Some(ss), _) => (ss.iter().map(|s| (s.now, s.order)).min().unwrap(), ss.iter().map(|s| (s.now, s.order)).max().unwrap()),
            (None, Some(_)) => ((e.now, FIRST), (e.ret.max(e.now), LAST)),
            (None, None) => continue,
        };
        items.push((from.0, from.1, 0, e.id, Event::Invoke { call: e.id, req: e.req.clone() }));
        if let Some((status, data)) = &e.outcome {
            let (kind, _) = encode(&e.req, WORKER);
            items.push((to.0, to.1, 1, e.id, Event::Return { call: e.id, res: decode(kind, *status, data) }));
        }
    }
    for s in &steps {
        let Some(step) = &s.step else { continue };
        let call = STEP_CALLS + s.order;
        items.push((s.now, s.order, 2, call, Event::Invoke { call, req: Request::Step(step.clone()) }));
        items.push((s.now, s.order, 3, call, Event::Return { call, res: Response::Status(200) }));
    }
    for (i, s) in sent.iter().enumerate() {
        items.push((s.at, LAST, 4, i as u64, Event::Receive { msg: s.msg.clone() }));
    }
    items.sort_by_key(|(t, slot, rank, id, _)| (*t, *slot, *rank, *id));
    let mut out = Vec::new();
    let mut clock: Option<u64> = None;
    for (t, _, _, _, e) in items {
        if clock.is_none_or(|c| t > c) {
            out.push(Event::Clock { at: t });
            clock = Some(t);
        }
        out.push(e);
    }
    out
}

#[derive(Debug)]
pub enum Verdict {
    /// Explained: how many nodes the search visited.
    Ok { explored: usize },
    /// No execution explains the event at `index`.
    Ko(Violation),
    /// The checker gave up before deciding.
    Unknown(Violation),
}

/// The trace against the model, partitioned by origin, with `budget` nodes
/// to explore at most. `retry_timeout`: the nodes' and the model's.
pub fn check(trace: &Trace, retry_timeout: u64, budget: u64) -> Verdict {
    let mut cfg = Config { max_explore: budget as usize, ..Config::default() };
    // `ECHOD_SIM_WIDTH=n`: give up at a narrower profile, to see what it holds.
    if let Some(w) = std::env::var("ECHOD_SIM_WIDTH").ok().and_then(|v| v.parse().ok()) {
        cfg.max_width = w;
    }
    let model = Resonate { retry_timeout, reported: true };
    let mut c: Checker<Grouped<Resonate>> = Checker::with_partitions(model, Server::default(), cfg).dominating(dominates);
    // `ECHOD_SIM_PROGRESS=n`: a line every n events, for where the time goes.
    let progress: Option<usize> = std::env::var("ECHOD_SIM_PROGRESS").ok().and_then(|v| v.parse().ok()).filter(|n| *n > 0);
    let started = std::time::Instant::now();
    let mut run = || -> Result<(), Violation> {
        for (i, e) in trace.iter().enumerate() {
            if progress.is_some_and(|n| i % n == 0) {
                let widths: Vec<usize> = c.factors().iter().map(|f| f.nodes.len()).collect();
                eprintln!("event {i}: {:.1?} explored {} max_width {} subsumed {} factors {:?}", started.elapsed(), c.stats.explored, c.stats.max_width, c.stats.subsumed, widths);
            }
            c.observe(e.clone()).map_err(|v| Violation { index: i, ..v })?;
        }
        Ok(())
    };
    match run() {
        Ok(_) => Verdict::Ok { explored: c.stats.explored },
        Err(v) if v.unknown => Verdict::Unknown(v),
        Err(v) => Verdict::Ko(v),
    }
}

/// The trace as a client saw it, one event per line, up to event `upto`.
pub fn show(trace: &Trace, upto: usize) -> String {
    let mut out = String::new();
    for (i, e) in trace.iter().enumerate().take(upto + 1) {
        let line = match e {
            Event::Invoke { call, req: Request::Step(st) } => format!("step {:>4} → {st:?}", call - STEP_CALLS),
            Event::Return { call, .. } if *call >= STEP_CALLS => format!("step {:>4} ←", call - STEP_CALLS),
            Event::Invoke { call, req } => format!("call {call:>4} → {req:?}"),
            Event::Return { call, res } => format!("call {call:>4} ← {res:?}"),
            Event::Receive { msg } => format!("          ⇐ {msg:?}"),
            Event::Clock { at } => format!("          ⏲ clock {at}"),
        };
        out.push_str(&format!("{i:>5}  {line}\n"));
    }
    out
}
