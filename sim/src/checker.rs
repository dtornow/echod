//! A run as a trace of the Resonate model, checked by `accordant`.
//!
//! The history becomes the checker's trace: every request a client made is
//! an `Invoke` at the instant it was sent (the injected clock's current
//! instant) and, if it was
//! answered, a `Return` at the instant the answer came; every message the
//! bus carried is a `Receive`; and the clock moves (`Clock`) at every
//! instant something happened, the nodes' own steps included. The checker
//! then asks whether some execution of the model, with its internal work (a
//! deadline, a lease, a resume, a retry, a schedule's occurrence) placed
//! where the checker likes, shows exactly these observations. Nothing of the
//! nodes' own account enters but the instants: the check is black-box. The
//! model is partitioned by origin, as the documents are.
//!
//! One clock. A request is decided at its invoke time, or at the document's
//! stamp if that is later; the stamp is an instant some step was
//! decided at, which the trace carries as a clock move. So the run's nodes
//! must keep the one clock too: with skew, drift or jumps a node sweeps at
//! an instant of its own, and the model, whose deadlines are exact, would
//! see a deadline fire early or late.

use accordant::{Checker, Config, Event, Grouped, Violation};
use resonate::{Dispatch, Request, Resonate, Response, Server};

use crate::bus::Sent;
use crate::history::Entry;
use crate::wire::{decode, encode};
use crate::workload::WORKER;

pub type Trace = Vec<Event<Request, Response, Dispatch>>;

/// The trace, from what the run recorded.
pub fn trace(entries: &[Entry], marks: &[u64], sent: &[Sent]) -> Trace {
    // (instant, rank, event): at one instant, returns and receives before
    // invokes, so a call never returns before it is invoked in the trace
    // order and a message is received where the clock had already reached.
    // The clock moves to the instants the nodes stamp at: a request's
    // invoke time, and the nodes' own steps (`marks`). A return
    // or a receive moves it nowhere: nothing is stamped at those instants,
    // and every instant the clock visits while a call is open is one more
    // place the model may land its effect.
    let mut items: Vec<(u64, u8, u64, Event<Request, Response, Dispatch>)> = Vec::new();
    for e in entries {
        items.push((e.now, 2, e.id, Event::Invoke { call: e.id, req: e.req.clone() }));
        if let Some((status, data)) = &e.outcome {
            let (kind, _) = encode(&e.req, WORKER);
            items.push((e.ret.max(e.now), 3, e.id, Event::Return { call: e.id, res: decode(kind, *status, data) }));
        }
    }
    for (i, s) in sent.iter().enumerate() {
        items.push((s.at, 1, i as u64, Event::Receive { msg: s.msg.clone() }));
    }
    items.sort_by_key(|(t, rank, id, _)| (*t, *rank, *id));
    let mut marks = marks.to_vec();
    marks.sort_unstable();
    let mut out = Vec::new();
    let mut clock: Option<u64> = None;
    let mut mi = 0;
    for (t, rank, _, e) in items {
        // the nodes' own instants up to here, then this one if it is an invoke
        while mi < marks.len() && marks[mi] <= t {
            if clock.is_none_or(|c| marks[mi] > c) {
                out.push(Event::Clock { at: marks[mi] });
                clock = Some(marks[mi]);
            }
            mi += 1;
        }
        if rank == 2 && clock.is_none_or(|c| t > c) {
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
/// to explore at most. `retry_timeout`: the nodes' and the model's;
/// `fire_within`: how long after its instant a schedule's occurrence is owed,
/// the nodes' sweep.
pub fn check(trace: &Trace, retry_timeout: u64, fire_within: u64, budget: u64) -> Verdict {
    let mut cfg = Config { max_explore: budget as usize, ..Config::default() };
    // `ECHOD_SIM_WIDTH=n`: give up at a narrower profile, to see what it holds.
    if let Some(w) = std::env::var("ECHOD_SIM_WIDTH").ok().and_then(|v| v.parse().ok()) {
        cfg.max_width = w;
    }
    let mut c: Checker<Grouped<Resonate>> = Checker::with_partitions(Resonate { retry_timeout, fire_within }, Server::default(), cfg);
    // The history is whole: a call it never answers may have taken effect at
    // any point or never, and a candidate still holding it subsumes one that
    // applied it.
    let mut open = std::collections::BTreeSet::new();
    for e in trace {
        match e {
            Event::Invoke { call, .. } => {
                open.insert(*call);
            }
            Event::Return { call, .. } => {
                open.remove(call);
            }
            _ => {}
        }
    }
    c.never_answered(open);
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
            Event::Invoke { call, req } => format!("call {call:>4} → {req:?}"),
            Event::Return { call, res } => format!("call {call:>4} ← {res:?}"),
            Event::Receive { msg } => format!("          ⇐ {msg:?}"),
            Event::Clock { at } => format!("          ⏲ clock {at}"),
        };
        out.push_str(&format!("{i:>5}  {line}\n"));
    }
    out
}
