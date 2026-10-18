//! The internal steps a node runs around a request, as pure functions of the
//! state: what a request leaves owed, and what a deadline fires. Shared by
//! the applier and by any model that must behave exactly like it.

use echod_kernel::{Config, Promise, PromiseState, State, TaskState};

/// Discharge every settled promise's callbacks and listeners, then fire
/// every retry that is due, until nothing is owed.
pub fn drain(s: &mut State, now: u64, cfg: &Config) {
    let mut rounds = 0;
    loop {
        rounds += 1;
        let mut did = false;
        let owed: Vec<(String, Vec<String>, Vec<String>)> = s
            .objects
            .iter()
            .filter(|p| p.state != PromiseState::Pending)
            .filter(|p| !p.callbacks.is_empty() || !p.listeners.is_empty())
            .map(|p| (p.id.clone(), p.callbacks.clone(), p.listeners.clone()))
            .collect();
        for (awaited, callbacks, listeners) in owed {
            for awaiter in callbacks {
                s.process_callback(&echod_kernel::PromiseRegisterCallbackReq { awaited: awaited.clone(), awaiter }, now, cfg);
                did = true;
            }
            for address in listeners {
                s.process_listener(&echod_kernel::PromiseRegisterListenerReq { awaited: awaited.clone(), address }, now, cfg);
                did = true;
            }
        }
        let due: Vec<String> = s
            .objects
            .iter()
            .filter(|p| p.state == PromiseState::Pending)
            .filter(|p| p.task.as_ref().map(|t| t.state == TaskState::Pending && t.retry_timeout_at.map(|d| d <= now).unwrap_or(false)).unwrap_or(false))
            .map(|p| p.id.clone())
            .collect();
        for id in due {
            s.process_retry_timeout(&echod_kernel::TaskRetryTimeoutReq { id }, now, cfg);
            did = true;
        }
        if !did || rounds > 64 {
            return;
        }
    }
}

/// Fire what is due in a document at `now`: deadlines, leases, retries.
pub fn sweep(s: &mut State, now: u64, cfg: &Config) {
    let ids: Vec<String> = s.objects.iter().map(|p| p.id.clone()).collect();
    for id in ids {
        s.process_promise_timeout(&echod_kernel::PromiseTimeoutReq { id: id.clone() }, now, cfg);
        s.process_lease_timeout(&echod_kernel::TaskLeaseTimeoutReq { id: id.clone() }, now, cfg);
        s.process_retry_timeout(&echod_kernel::TaskRetryTimeoutReq { id }, now, cfg);
    }
}

/// The nearest deadline a document owes a timer for.
pub fn next_deadline(rows: &[Promise]) -> Option<u64> {
    let mut min: Option<u64> = None;
    let mut note = |d: u64| min = Some(min.map_or(d, |m| m.min(d)));
    for p in rows {
        if p.state == PromiseState::Pending && echod_kernel::tags::exec_otype(&p.tags) != echod_kernel::tags::OType::Internal {
            note(p.timeout_at);
        }
        if let Some(t) = &p.task {
            if let Some(d) = t.retry_timeout_at {
                note(d);
            }
            if let Some(d) = t.lease_timeout_at {
                note(d);
            }
        }
    }
    min
}

/// The instant a step on `rows` is decided at: never earlier than any instant
/// the rows already record. The kernel's invariant has every `created_at`
/// and `settled_at` at or before `now`; a node whose clock is behind another
/// node's, or behind its own earlier self, would otherwise step outside what
/// the kernel is proved for. The clamp makes each origin's clock monotone
/// across the nodes that serve it.
pub fn clamp_now(rows: &[Promise], now: u64) -> u64 {
    rows.iter().fold(now, |n, p| n.max(p.created_at).max(p.settled_at.unwrap_or(0)))
}
