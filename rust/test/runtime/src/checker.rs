//! A run as a trace of the Resonate model, checked by Rover.
//!
//! The history becomes a Rover boundary trace: every request a client made is
//! an `Invoke` at the instant it was sent (its `head.debug_time`, the
//! earliest the node decides it at, which its retries keep) and, if it was
//! answered, a `Return` at the instant the answer came; every emitted message
//! is a `Receive`; and the clock moves (`Clock`) at every
//! instant something happened, the nodes' own steps included. The checker
//! then asks whether some execution of the model, with its internal work (a
//! deadline, a lease, a resume, a retry, a schedule's occurrence) placed
//! where Rover search places it, shows exactly these observations. Nothing of the
//! nodes' own account enters but the instants: the check is black-box. The
//! nodes' internal account enters.
//!
//! One clock. A request is decided at its `head.debug_time`, or at the
//! document's stamp if that is later; the stamp is an instant some step was
//! decided at, which the trace carries as a clock move. So the run's nodes
//! must keep the one clock too: with skew, drift or jumps a node sweeps at
//! an instant of its own, and the model, whose deadlines are exact, would
//! see a deadline fire early or late.

use echod_abstract_spec::Config;
use echod_abstract_exec::Spec as AbstractExec;
use echod_model_test::{history_rank, history_responses, rover_trace, HistoryEvent};
use rover_exec::{check as check_trace, CheckConfig};

use crate::history::Entry;
use crate::sim::Sent;

pub type Trace = Vec<HistoryEvent>;

/// The trace, from what the run recorded.
pub fn trace(entries: &[Entry], marks: &[u64], sent: &[Sent]) -> Trace {
    // At one instant, an invocation precedes the dispatch it can cause,
    // and the response follows both.
    // The clock moves to the instants the nodes stamp at: a request's
    // `debug_time`, its invoke, and the nodes' own steps (`marks`). A return
    // or a receive moves it nowhere: nothing is stamped at those instants,
    // and every instant the clock visits while a call is open is one more
    // place the model may land its effect.
    let mut items: Vec<(u64, u8, u64, HistoryEvent)> = Vec::new();
    for e in entries {
        items.push((
            e.now,
            0,
            e.id,
            HistoryEvent::Invoke {
                call: e.id,
                req: e.req.clone(),
            },
        ));
        if let Some(response) = &e.outcome {
            items.push((
                e.ret.max(e.now),
                2,
                e.id,
                HistoryEvent::Return {
                    call: e.id,
                    res: response.clone(),
                },
            ));
        }
    }
    for (i, s) in sent.iter().enumerate() {
        items.push((
            s.at,
            1,
            i as u64,
            HistoryEvent::Receive { msg: s.msg.clone() },
        ));
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
                out.push(HistoryEvent::Clock { at: marks[mi] });
                clock = Some(marks[mi]);
            }
            mi += 1;
        }
        if rank == 0 && clock.is_none_or(|c| t > c) {
            out.push(HistoryEvent::Clock { at: t });
            clock = Some(t);
        }
        out.push(e);
    }
    out
}

#[derive(Debug)]
pub struct Violation {
    pub index: usize,
    pub reason: String,
}

#[derive(Debug)]
pub enum Verdict {
    /// Explained: how many nodes the search visited.
    Ok { explored: usize },
    /// The checker gave up before deciding.
    Unknown(Violation),
}

/// The trace against the Echod abstract model. `retry_timeout` is the nodes' and the
/// model's; `budget` caps the certificate depth.
pub fn check(trace: &Trace, retry_timeout: u64, budget: u64) -> Verdict {
    let events = rover_trace(trace);
    let expected = history_responses(trace);
    let mut limits = CheckConfig::for_trace_len(events.len());
    limits.max_nodes = budget as usize;
    match check_trace(
        &AbstractExec,
        &Config { retry_timeout },
        &events,
        limits,
        |event, action, sent| history_rank(event, action, sent, &expected),
    ) {
        Some(certificate) => Verdict::Ok {
            explored: certificate.len(),
        },
        None => Verdict::Unknown(Violation {
            index: trace.len().saturating_sub(1),
            reason: "bounded Rover search found no certificate".into(),
        }),
    }
}

/// The trace as a client saw it, one event per line, up to event `upto`.
pub fn show(trace: &Trace, upto: usize) -> String {
    let mut out = String::new();
    for (i, e) in trace.iter().enumerate().take(upto + 1) {
        let line = match e {
            HistoryEvent::Invoke { call, req } => format!("call {call:>4} → {req:?}"),
            HistoryEvent::Return { call, res } => format!("call {call:>4} ← {res:?}"),
            HistoryEvent::Receive { msg } => format!("          ⇐ {msg:?}"),
            HistoryEvent::Clock { at } => format!("          ⏲ clock {at}"),
        };
        out.push_str(&format!("{i:>5}  {line}\n"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use echod_abstract_spec::Dispatch;
    use echod_types::{PromiseGetReq, Request};

    #[test]
    fn a_message_follows_the_invoke_that_shares_its_instant() {
        let at = 1_700_000_004_918;
        let entry = Entry {
            id: 214,
            client: "client".into(),
            req: Request::PromiseGet(PromiseGetReq { id: "o2:3".into() }),
            now: at,
            invoke: at,
            ret: at,
            outcome: Some(echod_types::Response::Promise(echod_types::PromiseRes {
                status: 404,
                promise: None,
            })),
            attempts: 1,
        };
        let sent = Sent {
            at,
            address: "sim://worker".into(),
            kind: "execute".into(),
            id: "o2:3".into(),
            msg: Dispatch::Execute { id: "o2:3".into(), version: 0 },
        };
        let events = trace(&[entry], &[], &[sent]);
        let clock = events.iter().position(|e| matches!(e, HistoryEvent::Clock { at: t } if *t == at)).unwrap();
        let invoke = events.iter().position(|e| matches!(e, HistoryEvent::Invoke { call: 214, .. })).unwrap();
        let receive = events.iter().position(|e| matches!(e, HistoryEvent::Receive { .. })).unwrap();
        let ret = events.iter().position(|e| matches!(e, HistoryEvent::Return { call: 214, .. })).unwrap();
        assert!(clock < invoke && invoke < receive && receive < ret);
    }
}
