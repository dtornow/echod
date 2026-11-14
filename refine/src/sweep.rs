//! The sweep as a function of the state: the kernel's six internal steps,
//! object by object, in the order the Resonate model runs them. A promise
//! past its deadline settles; a lease past its end is reclaimed; a callback
//! on a settled promise resumes its awaiter; a settled promise's listeners are
//! told; a pending task whose offer is due is offered again. Each phase only
//! enables work of a later phase, so one pass leaves nothing due.
//!
//! Three steps are the kernel's own functions (`promise_timeout_objects`,
//! `lease_timeout_objects`, `retry_timeout_objects`); `callback_fn` and
//! `listener_fn` write out what `process_callback` and `process_listener`
//! compute, which the kernel states as shapes (`resumed_shape`).

use vstd::prelude::*;

use echod_kernel::external::with_objects;
use echod_kernel::internal::{lease_timeout_objects, promise_timeout_objects, retry_due, retry_timeout_objects};
use echod_kernel::properties::opt_or_zero;
use echod_kernel::steps::{is_next, lease_deadline, retry_deadline, strip};
use echod_kernel::store::AState;
use echod_kernel::tags::target_of;
use echod_kernel::types::*;
use resonate::spec::DispatchV;

use crate::translate::message_out;

verus! {

/// `processCallback`: a settled promise's callback resumes its awaiter. The
/// awaited is read and projected; a pending one, or one without this callback,
/// ends the step. Else the callback is spent and the awaiter, read and
/// projected, is woken (suspended), told (running), or left (fulfilled).
pub open spec fn callback_fn(a: AState, x: Seq<char>, y: Seq<char>, now: nat) -> AState {
    if !a.objects.contains_key(x) {
        a
    } else {
        let p = a.objects[x].project(now);
        let a1 = with_objects(a, a.objects.insert(x, p));
        if p.state == PromiseState::Pending || !p.callbacks.contains(y) {
            a1
        } else {
            let a2 = with_objects(a1, a1.objects.insert(x, p.remove_callback(y)));
            if !a2.objects.contains_key(y) {
                a2
            } else {
                let q = a2.objects[y].project(now);
                let a3 = with_objects(a2, a2.objects.insert(y, q));
                match q.task {
                    None => a3,
                    Some(t) => {
                        if t.state == TaskState::Suspended {
                            with_objects(a3, a3.objects.insert(y, q.with_task(t.wake(x, opt_or_zero(p.settled_at)))))
                        } else if t.state != TaskState::Fulfilled {
                            with_objects(a3, a3.objects.insert(y, q.with_task(t.buffer(x))))
                        } else {
                            a3
                        }
                    },
                }
            }
        }
    }
}

/// `processListener`: a settled promise's listener is told, once.
pub open spec fn listener_fn(a: AState, x: Seq<char>, address: Seq<char>, now: nat) -> AState {
    if !a.objects.contains_key(x) {
        a
    } else {
        let p = a.objects[x].project(now);
        let a1 = with_objects(a, a.objects.insert(x, p));
        if p.state == PromiseState::Pending || !p.listeners.contains(address) {
            a1
        } else {
            let q = p.remove_listener(address);
            AState {
                objects: a1.objects.insert(x, q),
                outbox: a1.outbox.insert(OutboxKey::Notify(x, address), AOutboxEntry { address, message: AMessage::Unblock(q.to_record()) }),
                ..a1
            }
        }
    }
}

/// `processRetryTimeout`: a due offer is re-armed on the grid and the task
/// offered to its target.
pub open spec fn retry_fn(a: AState, id: Seq<char>, now: nat, retry_timeout: nat) -> AState {
    if a.objects.contains_key(id) && retry_due(a.objects[id], now) {
        let p = a.objects[id];
        AState {
            objects: retry_timeout_objects(a, id, now, retry_timeout),
            outbox: a.outbox.insert(
                OutboxKey::Execute(id),
                AOutboxEntry { address: target_of(p.tags), message: AMessage::Execute { task_id: id, version: p.task.unwrap().version } },
            ),
            ..a
        }
    } else {
        a
    }
}

// ------------------------------------------------------------------- phases

pub open spec fn phase_deadlines(a: AState, ids: Seq<Seq<char>>, now: nat) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        let a1 = phase_deadlines(a, ids.drop_last(), now);
        with_objects(a1, promise_timeout_objects(a1, ids.last(), now))
    }
}

pub open spec fn phase_leases(a: AState, ids: Seq<Seq<char>>, now: nat) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        let a1 = phase_leases(a, ids.drop_last(), now);
        with_objects(a1, lease_timeout_objects(a1, ids.last(), now))
    }
}

/// Every callback stored on `x` is spent, in the stored order.
pub open spec fn callbacks_of(a: AState, x: Seq<char>, awaiters: Seq<Seq<char>>, now: nat) -> AState
    decreases awaiters.len(),
{
    if awaiters.len() == 0 {
        a
    } else {
        callback_fn(callbacks_of(a, x, awaiters.drop_last(), now), x, awaiters.last(), now)
    }
}

pub open spec fn phase_callbacks(a: AState, ids: Seq<Seq<char>>, now: nat) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        let a1 = phase_callbacks(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            callbacks_of(a1, x, a1.objects[x].callbacks, now)
        } else {
            a1
        }
    }
}

pub open spec fn listeners_of(a: AState, x: Seq<char>, addresses: Seq<Seq<char>>, now: nat) -> AState
    decreases addresses.len(),
{
    if addresses.len() == 0 {
        a
    } else {
        listener_fn(listeners_of(a, x, addresses.drop_last(), now), x, addresses.last(), now)
    }
}

pub open spec fn phase_listeners(a: AState, ids: Seq<Seq<char>>, now: nat) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        let a1 = phase_listeners(a, ids.drop_last(), now);
        let x = ids.last();
        if a1.objects.contains_key(x) {
            listeners_of(a1, x, a1.objects[x].listeners, now)
        } else {
            a1
        }
    }
}

pub open spec fn phase_retries(a: AState, ids: Seq<Seq<char>>, now: nat, retry_timeout: nat) -> AState
    decreases ids.len(),
{
    if ids.len() == 0 {
        a
    } else {
        retry_fn(phase_retries(a, ids.drop_last(), now, retry_timeout), ids.last(), now, retry_timeout)
    }
}

/// The objects, in some definite order.
pub open spec fn ids_of(a: AState) -> Seq<Seq<char>> {
    a.objects.dom().to_seq()
}

/// The sweep: nothing due is left on any object.
pub open spec fn sweep_fn(a: AState, now: nat, retry_timeout: nat) -> AState {
    let ids = ids_of(a);
    let a1 = phase_deadlines(a, ids, now);
    let a2 = phase_leases(a1, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    phase_retries(a4, ids, now, retry_timeout)
}

// ------------------------------------------------------------- what is sent
//
// The sweep's dispatches as a sequence: what each listener step and each
// retry step sends, in the order the phases run them. The outbox entries the
// steps write are the same messages; the sequence is what the machine sends.

/// What one listener step sends: the unblock, if it fires.
pub open spec fn listener_send(a: AState, x: Seq<char>, address: Seq<char>, now: nat) -> Seq<DispatchV> {
    if a.objects.contains_key(x) && a.objects[x].project(now).state != PromiseState::Pending && a.objects[x].project(now).listeners.contains(address) {
        let q = a.objects[x].project(now).remove_listener(address);
        seq![message_out(AOutboxEntry { address, message: AMessage::Unblock(q.to_record()) })]
    } else {
        Seq::empty()
    }
}

pub open spec fn listeners_sends(a: AState, x: Seq<char>, addresses: Seq<Seq<char>>, now: nat) -> Seq<DispatchV>
    decreases addresses.len(),
{
    if addresses.len() == 0 {
        Seq::empty()
    } else {
        listeners_sends(a, x, addresses.drop_last(), now) + listener_send(listeners_of(a, x, addresses.drop_last(), now), x, addresses.last(), now)
    }
}

pub open spec fn phase_listeners_sends(a: AState, ids: Seq<Seq<char>>, now: nat) -> Seq<DispatchV>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        let a1 = phase_listeners(a, ids.drop_last(), now);
        let x = ids.last();
        phase_listeners_sends(a, ids.drop_last(), now) + (if a1.objects.contains_key(x) { listeners_sends(a1, x, a1.objects[x].listeners, now) } else { Seq::empty() })
    }
}

/// What one retry step sends: the offer, if it fires.
pub open spec fn retry_send(a: AState, id: Seq<char>, now: nat, retry_timeout: nat) -> Seq<DispatchV> {
    if a.objects.contains_key(id) && retry_due(a.objects[id], now) {
        let p = a.objects[id];
        seq![message_out(AOutboxEntry { address: target_of(p.tags), message: AMessage::Execute { task_id: id, version: p.task.unwrap().version } })]
    } else {
        Seq::empty()
    }
}

pub open spec fn phase_retries_sends(a: AState, ids: Seq<Seq<char>>, now: nat, retry_timeout: nat) -> Seq<DispatchV>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        phase_retries_sends(a, ids.drop_last(), now, retry_timeout) + retry_send(phase_retries(a, ids.drop_last(), now, retry_timeout), ids.last(), now, retry_timeout)
    }
}

/// What the sweep sends: the listeners told, then the tasks offered.
pub open spec fn sweep_sends(a: AState, now: nat, retry_timeout: nat) -> Seq<DispatchV> {
    let ids = ids_of(a);
    let a1 = phase_deadlines(a, ids, now);
    let a2 = phase_leases(a1, ids, now);
    let a3 = phase_callbacks(a2, ids, now);
    let a4 = phase_listeners(a3, ids, now);
    phase_listeners_sends(a3, ids, now) + phase_retries_sends(a4, ids, now, retry_timeout)
}

/// The model's deadlines of an object: a pending promise's timeout, whatever
/// its kind (the model arms a timer for every live promise); a lease's end;
/// an offer. The kernel's `deadline_at` leaves internal promises out.
pub open spec fn mdeadline_at(p: APromise, t: nat) -> bool {
    ||| p.state == PromiseState::Pending && p.timeout_at as nat == t
    ||| lease_deadline(p) == Some(t)
    ||| retry_deadline(p) == Some(t)
}

/// The state's next deadline, if it has one: when the next sweep is due.
pub open spec fn next_deadline(a: AState) -> Option<nat> {
    if exists|t: nat| is_next(strip(a), t) {
        Some(choose|t: nat| is_next(strip(a), t))
    } else {
        None
    }
}

} // verus!
