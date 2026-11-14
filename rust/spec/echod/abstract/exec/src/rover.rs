//! Executable Rover process realization of `echod_abstract_spec::Proc`.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use rover_spec::rover::comm::{ProcessEvent, Time};
use rover_spec::rover::RoverSpec::{Spec as _, StepResultV};
use echod_types::{Request, Response};
use crate::projection::group_views as group_exec_views;
use crate::runtime::copy;
use crate::state::{unavailable, Handlers, InOut, Out, Store, Work};
use echod_types::{Call, Dispatch, DispatchV, Message, Output};
use echod_abstract_spec::state::Config;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::axioms::pset_seq;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::spec_handler;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::rover::{
    empty_store, lemma_losses_map, remove_at, spec_derived, spec_due_result, spec_idle,
    spec_internal_result, spec_keep, spec_lose, spec_losses, spec_over_callbacks,
    spec_over_listeners, spec_over_promises, spec_over_schedules, spec_over_tasks, spec_queue,
    spec_ready, spec_request_outcome, spec_run, spec_run_timeout, spec_send, spec_service,
    spec_shed,
};
use echod_abstract_spec::rover::{Pid, Proc as SpecProc, Spec as SpecModel};
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::*;
#[cfg(verus_keep_ghost)]
use echod_abstract_spec::state::spec_body;

verus! {
#[derive(Clone, PartialEq, Eq, Debug)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Proc {
    pub store: Store,
    pub pending: Vec<Work>,
}

pub struct ProcessResult {
    pub state: Proc,
    pub send: Vec<(Pid, Message)>,
    pub marks: Vec<&'static str>,
}

impl View for Proc {
    type V = SpecProc;

    open spec fn view(&self) -> SpecProc {
        SpecProc {
            store: self.store@,
            pending: self.pending@.map_values(|work: Work| crate::projection::as_sched(work)),
        }
    }
}

fn initial_store() -> (server: Store)
    ensures
        server@ == empty_store(),
{
    let server = Store {
        promises: crate::collections::PMap::empty(),
        tasks: crate::collections::PMap::empty(),
        schedules: crate::collections::PMap::empty(),
    };
    proof {
        broadcast use group_exec_views;
        assert(server.promises@.map_values(|p: crate::state::Promise| p@) =~= Map::empty());
        assert(server.tasks@.map_values(|t: crate::state::Task| t@) =~= Map::empty());
        assert(server.schedules@.map_values(|s: echod_types::Schedule| schedule_v(s)) =~= Map::empty());
    }
    server
}

/// The results of a step, as the trait reads them.
pub open spec fn results_v(results: Seq<ProcessResult>) -> Seq<StepResultV<SpecProc, Pid, Message>> {
    results.map_values(|result: ProcessResult| StepResultV {
        state: result.state@,
        send: result.send@,
    })
}

fn send(
    call: &Call,
    response: Response,
    mut dispatches: Vec<Dispatch>,
) -> (messages: Vec<(Pid, Message)>)
    ensures
        messages@ == spec_send(*call, response, dispatches@.map_values(|d: Dispatch| d@)),
{
    let ghost all = dispatches@;
    let ghost response_value = response;
    let mut messages = Vec::new();
    let first = (
        Pid::Outside,
        Message::Output(Output::Response {
            client: copy(&call.client),
            id: call.id,
            response,
        }),
    );
    messages.push(first);
    while !dispatches.is_empty()
        invariant
            messages@.len() >= 1,
            messages@[0] == first,
            messages@.len() + dispatches@.len() == 1 + all.len(),
            dispatches@ == all.skip(messages@.len() - 1),
            messages@.skip(1) == all
                .take(messages@.len() - 1)
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                )),
        decreases dispatches.len(),
    {
        let ghost i = messages@.len() as int - 1;
        assert(dispatches@.len() > 0);
        assert(i + dispatches@.len() == all.len());
        assert(0 <= i);
        assert(i < all.len());
        assert(0 <= i < all.len());
        let ghost before = messages@;
        let dispatch = dispatches.remove(0);
        assert(dispatch == all[i]);
        assert(all.skip(i).remove(0) =~= all.skip(i + 1));
        assert(all.take(i + 1) =~= all.take(i).push(all[i]));
        messages.push((
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        ));
        proof {
            assert(messages@ == before.push((
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )));
            assert(messages@.skip(1) == before.skip(1).push((
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )));
            assert(all.take(i + 1).map_values(|dispatch: Dispatch| (
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )) =~= all.take(i).map_values(|dispatch: Dispatch| (
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )).push((
                Pid::Outside,
                Message::Output(Output::Dispatch(all[i])),
            )));
            assert(messages@.skip(1) =~= all
                .take(i + 1)
                .map_values(|dispatch: Dispatch| (
                    Pid::Outside,
                    Message::Output(Output::Dispatch(dispatch)),
                )));
        }
    }
    proof {
        assert(all.take(all.len() as int) =~= all);
        assert(messages@.skip(1) =~= all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )));
        assert forall|i: int| 0 <= i < all.len() implies
            lift_dispatch(all[i]@) == all[i] by {
            lemma_lift_dispatch(all[i]);
        }
        assert(all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        )) =~= all.map_values(|dispatch: Dispatch| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                lift_dispatch(dispatch@),
            )),
        )));
        assert(first == (
            Pid::Outside,
            Message::Output(Output::Response {
                client: call.client,
                id: call.id,
                response: response_value,
            }),
        ));
        assert(messages@ =~= seq![messages@[0]] + messages@.skip(1));
        assert(messages@ =~= spec_send(*call, response_value, all.map_values(|d: Dispatch| d@)));
    }
    messages
}

fn append_work(
    pending: &Vec<Work>,
    mut work: Vec<Work>,
) -> (result: Vec<Work>)
    ensures
        result@.map_values(|item: Work| crate::projection::as_sched(item))
            == pending@.map_values(|item: Work| crate::projection::as_sched(item))
                + work@.map_values(|item: Work| crate::projection::as_sched(item)),
{
    let mut result = copy(pending);
    result.append(&mut work);
    result
}

fn request_outcome(
    before: &Proc,
    call: &Call,
    outcome: Out,
) -> (result: ProcessResult)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_request_outcome(before@, *call, outcome@),
{
    let Out {
        resp,
        next,
        work,
        send: dispatches,
        marks,
    } = outcome;
    ProcessResult {
        state: Proc {
            store: next,
            pending: append_work(&before.pending, work),
        },
        send: send(call, resp, dispatches),
        marks,
    }
}

fn lose_outcome(
    before: &Proc,
    call: &Call,
    outcome: Out,
) -> (result: ProcessResult)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_lose(before@, *call, outcome@),
{
    let Out {
        resp: _,
        next,
        work,
        send: dispatches,
        marks,
    } = outcome;
    ProcessResult {
        state: Proc {
            store: next,
            pending: append_work(&before.pending, work),
        },
        send: send(call, unavailable(&call.request), dispatches),
        marks,
    }
}

fn shed_outcome(before: &Proc, call: &Call) -> (result: ProcessResult)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_shed(before@, *call),
{
    let dispatches: Vec<Dispatch> = Vec::new();
    let result = ProcessResult {
        state: copy(before),
        send: send(call, unavailable(&call.request), dispatches),
        marks: Vec::new(),
    };
    proof {
        assert(dispatches@.map_values(|d: Dispatch| d@) =~= Seq::<DispatchV>::empty());
    }
    result
}

pub open spec fn spec_request_result(state: SpecProc, call: Call, lost: bool, o: Out) -> StepResultV<SpecProc, Pid, Message> {
    if lost { spec_lose(state, call, o@) } else { spec_request_outcome(state, call, o@) }
}

/// `outcomes`, one result each: served, or lost. Every request step is the
/// served outcomes, then the lost ones.
fn request_results(
    state: &Proc,
    call: &Call,
    mut outcomes: Vec<Out>,
    lost: bool,
) -> (results: Vec<ProcessResult>)
    ensures
        results_v(results@) == if lost {
            spec_losses(state@, *call, outcomes@.map_values(|o: Out| o@))
        } else {
            outcomes@.map_values(|o: Out| o@).map_values(|o: OutV| spec_request_outcome(state@, *call, o))
        },
{
    let ghost all = outcomes@;
    let mut results: Vec<ProcessResult> = Vec::new();
    while !outcomes.is_empty()
        invariant
            outcomes@ == all.skip(results@.len() as int),
            results@.len() + outcomes@.len() == all.len(),
            results_v(results@) == all.take(results@.len() as int).map_values(|o: Out| spec_request_result(state@, *call, lost, o)),
        decreases outcomes.len(),
    {
        let ghost i = results@.len() as int;
        let ghost before = results@;
        let outcome = outcomes.remove(0);
        assert(outcome == all[i]);
        assert(all.skip(i).remove(0) =~= all.skip(i + 1));
        assert(all.take(i + 1) =~= all.take(i).push(all[i]));
        let result = if lost { lose_outcome(state, call, outcome) } else { request_outcome(state, call, outcome) };
        proof {
            assert((StepResultV { state: result.state@, send: result.send@ }) == spec_request_result(state@, *call, lost, all[i]));
        }
        results.push(result);
        proof {
            assert(results@ == before.push(result));
            assert(results_v(results@).len() == results_v(before).len() + 1);
            assert(results_v(results@)[i] == spec_request_result(state@, *call, lost, all[i]));
            assert forall|j: int| 0 <= j < i implies results_v(results@)[j] == results_v(before)[j] by {}
            assert(results_v(results@) =~= results_v(before).push(spec_request_result(state@, *call, lost, all[i])));
            assert(all.take(i).push(all[i]).map_values(|o: Out| spec_request_result(state@, *call, lost, o)) =~= all.take(i).map_values(|o: Out| spec_request_result(state@, *call, lost, o)).push(spec_request_result(state@, *call, lost, all[i])));
        }
    }
    proof {
        assert(all.take(all.len() as int) =~= all);
        if lost {
            lemma_losses_map(state@, *call, all.map_values(|o: Out| o@));
            assert(all.map_values(|o: Out| spec_request_result(state@, *call, lost, o)) =~= spec_losses(state@, *call, all.map_values(|o: Out| o@)));
        } else {
            assert(all.map_values(|o: Out| spec_request_result(state@, *call, lost, o)) =~= all.map_values(|o: Out| o@).map_values(|o: OutV| spec_request_outcome(state@, *call, o)));
        }
    }
    results
}

fn run(
    config: &Config,
    state: &Proc,
    call: &Call,
    now: Time,
) -> (results: Vec<ProcessResult>)
    ensures
        results_v(results@) == spec_run(*config, state@, *call, now)
            + spec_losses(state@, *call, spec_handler(*config, call.request, state@.store, now))
            + seq![spec_shed(state@, *call)],
{
    let served = Handlers(config).handler(&call.request, &state.store, now);
    let mut results = request_results(state, call, served, false);
    let lost = Handlers(config).handler(&call.request, &state.store, now);
    let mut losses = request_results(state, call, lost, true);
    let ghost served_v = results_v(results@);
    let ghost lost_v = results_v(losses@);
    results.append(&mut losses);
    let shed = shed_outcome(state, call);
    results.push(shed);
    proof {
        assert(results_v(results@) =~= served_v + lost_v + seq![spec_shed(state@, *call)]);
    }
    results
}

fn ready(work: &Work, now: Time) -> (is_ready: bool)
    ensures
        is_ready == spec_ready(work@, now),
{
    match work {
        Work::Occurrence { at, .. } => *at <= now,
        _ => false,
    }
}

fn internal_result(
    before: &Proc,
    i: usize,
    outcome: InOut,
) -> (result: ProcessResult)
    requires
        i < before.pending.len(),
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_internal_result(before@, i as int, outcome@),
{
    let ghost outv = outcome@;
    let InOut {
        next,
        mut work,
        send: mut dispatches,
        marks,
        not_due: _,
    } = outcome;
    let mut pending = copy(&before.pending);
    pending.remove(i);
    pending.append(&mut work);
    let ghost all = dispatches@;
    let mut send = Vec::new();
    while !dispatches.is_empty()
        invariant
            send@.len() + dispatches@.len() == all.len(),
            dispatches@ == all.skip(send@.len() as int),
            send@ == all.take(send@.len() as int).map_values(|dispatch: Dispatch| (
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )),
        decreases dispatches.len(),
    {
        let ghost j = send@.len() as int;
        let dispatch = dispatches.remove(0);
        assert(dispatch == all[j]);
        assert(all.skip(j).remove(0) =~= all.skip(j + 1));
        assert(all.take(j + 1) =~= all.take(j).push(all[j]));
        send.push((
            Pid::Outside,
            Message::Output(Output::Dispatch(dispatch)),
        ));
    }
    proof {
        assert(pending@.map_values(|item: Work| crate::projection::as_sched(item))
            =~= remove_at(before@.pending, i as int) + outv.work);
        assert(all.take(all.len() as int) =~= all);
        assert forall|j: int| 0 <= j < outv.send.len() implies
            lift_dispatch(outv.send[j]) == all[j] by {
            lemma_lift_dispatch(all[j]);
        }
        assert(send@ =~= outv.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(
                lift_dispatch(dispatch),
            )),
        )));
    }
    ProcessResult {
        state: Proc {
            store: next,
            pending,
        },
        send,
        marks,
    }
}

fn run_timeout_from(
    config: &Config,
    state: &Proc,
    now: Time,
    i: usize,
) -> (results: Vec<ProcessResult>)
    requires
        i <= state.pending.len(),
    ensures
        results_v(results@) == spec_queue(*config, state@, now, i as int),
    decreases state.pending.len() - i,
{
    if i == state.pending.len() {
        let results: Vec<ProcessResult> = Vec::new();
        proof {
            assert(results_v(results@) =~= spec_queue(*config, state@, now, i as int));
        }
        return results;
    }
    let work = &state.pending[i];
    proof {
        assert(state@.pending[i as int] == crate::projection::as_sched(*work));
        assert(spec_body(crate::projection::as_sched(*work)) == work@);
    }
    let outcome = Handlers(config).process_work(work, &state.store, now);
    let is_ready = ready(work, now);
    let mut tail = run_timeout_from(config, state, now, i + 1);
    if is_ready && !outcome.not_due {
        let result = internal_result(state, i, outcome);
        let mut results = Vec::new();
        results.push(result);
        let ghost tail_v = results_v(tail@);
        results.append(&mut tail);
        proof {
            assert(results_v(results@) =~= seq![spec_internal_result(state@, i as int, outcome@)] + tail_v);
        }
        results
    } else {
        tail
    }
}

fn due_result(before: &Proc, outcome: InOut) -> (result: ProcessResult)
    ensures
        (StepResultV {
            state: result.state@,
            send: result.send@,
        }) == spec_due_result(before@, outcome@),
{
    let ghost outv = outcome@;
    let InOut { next, mut work, send: mut dispatches, marks, not_due: _ } = outcome;
    let mut pending = copy(&before.pending);
    pending.append(&mut work);
    let ghost all = dispatches@;
    let mut send = Vec::new();
    while !dispatches.is_empty()
        invariant
            send@.len() + dispatches@.len() == all.len(),
            dispatches@ == all.skip(send@.len() as int),
            send@ == all.take(send@.len() as int).map_values(|dispatch: Dispatch| (
                Pid::Outside,
                Message::Output(Output::Dispatch(dispatch)),
            )),
        decreases dispatches.len(),
    {
        let ghost j = send@.len() as int;
        let dispatch = dispatches.remove(0);
        assert(dispatch == all[j]);
        assert(all.skip(j).remove(0) =~= all.skip(j + 1));
        assert(all.take(j + 1) =~= all.take(j).push(all[j]));
        send.push((Pid::Outside, Message::Output(Output::Dispatch(dispatch))));
    }
    proof {
        assert(pending@.map_values(|item: Work| crate::projection::as_sched(item)) =~= before@.pending + outv.work);
        assert(all.take(all.len() as int) =~= all);
        assert forall|j: int| 0 <= j < outv.send.len() implies lift_dispatch(outv.send[j]) == all[j] by {
            lemma_lift_dispatch(all[j]);
        }
        assert(send@ =~= outv.send.map_values(|dispatch: DispatchV| (
            Pid::Outside,
            Message::Output(Output::Dispatch(lift_dispatch(dispatch))),
        )));
    }
    ProcessResult { state: Proc { store: next, pending }, send, marks }
}

/// One derived step, kept when its handler would do something: `spec_keep`.
fn keep(config: &Config, state: &Proc, now: Time, work: Work) -> (results: Vec<ProcessResult>)
    ensures
        results_v(results@) == spec_keep(*config, state@, now, work@, Seq::empty()),
{
    let outcome = Handlers(config).process_work(&work, &state.store, now);
    let mut results: Vec<ProcessResult> = Vec::new();
    if !outcome.not_due {
        results.push(due_result(state, outcome));
    }
    proof {
        assert(results_v(results@) =~= spec_keep(*config, state@, now, work@, Seq::empty()));
    }
    results
}

fn over_callbacks(
    config: &Config,
    state: &Proc,
    now: Time,
    awaited: &String,
    awaiters: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcessResult>)
    requires
        i <= awaiters.len(),
    ensures
        results_v(results@) == spec_over_callbacks(*config, state@, now, awaited@, strs(awaiters@).skip(i as int)),
    decreases awaiters.len() - i,
{
    broadcast use group_exec_views;
    if i == awaiters.len() {
        let results: Vec<ProcessResult> = Vec::new();
        proof {
            assert(strs(awaiters@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let awaiter = copy(&awaiters[i]);
    let mut results = keep(config, state, now, Work::Callback { awaited: copy(awaited), awaiter });
    let ghost head = results_v(results@);
    let mut rest = over_callbacks(config, state, now, awaited, awaiters, i + 1);
    let ghost tail = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(awaiters@).skip(i as int).drop_first() =~= strs(awaiters@).skip(i as int + 1));
        assert(strs(awaiters@).skip(i as int)[0] == awaiters@[i as int]@);
        assert(results_v(results@) =~= head + tail);
    }
    results
}

fn over_listeners(
    config: &Config,
    state: &Proc,
    now: Time,
    awaited: &String,
    addresses: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcessResult>)
    requires
        i <= addresses.len(),
    ensures
        results_v(results@) == spec_over_listeners(*config, state@, now, awaited@, strs(addresses@).skip(i as int)),
    decreases addresses.len() - i,
{
    broadcast use group_exec_views;
    if i == addresses.len() {
        let results: Vec<ProcessResult> = Vec::new();
        proof {
            assert(strs(addresses@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let address = copy(&addresses[i]);
    let mut results = keep(config, state, now, Work::Listener { awaited: copy(awaited), address });
    let ghost head = results_v(results@);
    let mut rest = over_listeners(config, state, now, awaited, addresses, i + 1);
    let ghost tail = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(addresses@).skip(i as int).drop_first() =~= strs(addresses@).skip(i as int + 1));
        assert(strs(addresses@).skip(i as int)[0] == addresses@[i as int]@);
        assert(results_v(results@) =~= head + tail);
    }
    results
}

fn over_promises(
    config: &Config,
    state: &Proc,
    now: Time,
    keys: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcessResult>)
    requires
        i <= keys.len(),
        forall|j: int| 0 <= j < keys.len() ==> state.store.promises@.contains_key(#[trigger] keys[j]@),
    ensures
        results_v(results@) == spec_over_promises(*config, state@, now, strs(keys@).skip(i as int)),
    decreases keys.len() - i,
{
    broadcast use group_exec_views;
    if i == keys.len() {
        let results: Vec<ProcessResult> = Vec::new();
        proof {
            assert(strs(keys@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let id = &keys[i];
    let p = match state.store.promises.get(id) {
        Some(p) => p,
        None => {
            proof {
                assert(false);
            }
            vstd::pervasive::unreached()
        }
    };
    let mut results = keep(config, state, now, Work::PromiseTimeout(copy(id)));
    let ghost a = results_v(results@);
    let callbacks = p.callbacks.to_vec();
    let mut over_cb = over_callbacks(config, state, now, id, &callbacks, 0);
    let ghost b = results_v(over_cb@);
    let listeners = p.listeners.to_vec();
    let mut over_ls = over_listeners(config, state, now, id, &listeners, 0);
    let ghost c = results_v(over_ls@);
    let mut rest = over_promises(config, state, now, keys, i + 1);
    let ghost d = results_v(rest@);
    results.append(&mut over_cb);
    results.append(&mut over_ls);
    results.append(&mut rest);
    proof {
        assert(strs(keys@).skip(i as int).drop_first() =~= strs(keys@).skip(i as int + 1));
        assert(strs(keys@).skip(i as int)[0] == id@);
        assert(strs(callbacks@).skip(0) =~= pset_seq(p@.callbacks));
        assert(strs(listeners@).skip(0) =~= pset_seq(p@.listeners));
        assert(state@.store.promises[id@] == p@);
        assert(results_v(results@) =~= a + b + c + d);
    }
    results
}

fn over_tasks(
    config: &Config,
    state: &Proc,
    now: Time,
    keys: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcessResult>)
    requires
        i <= keys.len(),
        forall|j: int| 0 <= j < keys.len() ==> state.store.tasks@.contains_key(#[trigger] keys[j]@),
    ensures
        results_v(results@) == spec_over_tasks(*config, state@, now, strs(keys@).skip(i as int)),
    decreases keys.len() - i,
{
    broadcast use group_exec_views;
    if i == keys.len() {
        let results: Vec<ProcessResult> = Vec::new();
        proof {
            assert(strs(keys@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let id = &keys[i];
    let t = match state.store.tasks.get(id) {
        Some(t) => t,
        None => {
            proof {
                assert(false);
            }
            vstd::pervasive::unreached()
        }
    };
    let mut results = keep(config, state, now, Work::TaskLeaseTimeout(copy(id)));
    let ghost lease = results_v(results@);
    let ghost retry: Seq<StepResultV<SpecProc, Pid, Message>>;
    match t.retry_timeout_at {
        Some(_) => {
            let mut again = keep(config, state, now, Work::TaskRetryTimeout(copy(id)));
            proof {
                retry = results_v(again@);
            }
            results.append(&mut again);
        }
        None => {
            proof {
                retry = Seq::empty();
            }
        }
    }
    let ghost sofar = results_v(results@);
    let mut rest = over_tasks(config, state, now, keys, i + 1);
    let ghost d = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(keys@).skip(i as int).drop_first() =~= strs(keys@).skip(i as int + 1));
        assert(strs(keys@).skip(i as int)[0] == id@);
        assert(state@.store.tasks[id@] == t@);
        assert(sofar =~= lease + retry);
        assert(results_v(results@) =~= lease + retry + d);
    }
    results
}

fn over_schedules(
    config: &Config,
    state: &Proc,
    now: Time,
    keys: &Vec<String>,
    i: usize,
) -> (results: Vec<ProcessResult>)
    requires
        i <= keys.len(),
        forall|j: int| 0 <= j < keys.len() ==> state.store.schedules@.contains_key(#[trigger] keys[j]@),
    ensures
        results_v(results@) == spec_over_schedules(*config, state@, now, strs(keys@).skip(i as int)),
    decreases keys.len() - i,
{
    broadcast use group_exec_views;
    if i == keys.len() {
        let results: Vec<ProcessResult> = Vec::new();
        proof {
            assert(strs(keys@).skip(i as int) =~= Seq::<Seq<char>>::empty());
            assert(results_v(results@) =~= Seq::empty());
        }
        return results;
    }
    let id = &keys[i];
    let c = match state.store.schedules.get(id) {
        Some(c) => c,
        None => {
            proof {
                assert(false);
            }
            vstd::pervasive::unreached()
        }
    };
    let promise = crate::runtime::expand(&c.promise_id, id, c.next_run_at);
    let mut results = keep(config, state, now, Work::ScheduleTimeout { id: copy(id), promise });
    let ghost head = results_v(results@);
    let mut rest = over_schedules(config, state, now, keys, i + 1);
    let ghost tail = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(strs(keys@).skip(i as int).drop_first() =~= strs(keys@).skip(i as int + 1));
        assert(strs(keys@).skip(i as int)[0] == id@);
        assert(state@.store.schedules[id@] == schedule_v(*c));
        assert(results_v(results@) =~= head + tail);
    }
    results
}

/// The steps the three maps offer, in the order the specification walks
/// them: `spec_derived`.
fn derived(config: &Config, state: &Proc, now: Time) -> (results: Vec<ProcessResult>)
    ensures
        results_v(results@) == spec_derived(*config, state@, now),
{
    broadcast use group_exec_views;
    let promises = state.store.promises.keys();
    let tasks = state.store.tasks.keys();
    let schedules = state.store.schedules.keys();
    let mut results = over_promises(config, state, now, &promises, 0);
    let ghost a = results_v(results@);
    let mut over_t = over_tasks(config, state, now, &tasks, 0);
    let ghost b = results_v(over_t@);
    let mut over_s = over_schedules(config, state, now, &schedules, 0);
    let ghost c = results_v(over_s@);
    results.append(&mut over_t);
    results.append(&mut over_s);
    proof {
        assert(strs(promises@).skip(0) =~= spec_keys(state@.store.promises));
        assert(strs(tasks@).skip(0) =~= spec_keys(state@.store.tasks));
        assert(strs(schedules@).skip(0) =~= spec_keys(state@.store.schedules));
        assert(results_v(results@) =~= a + b + c);
    }
    results
}

fn run_timeout(
    config: &Config,
    state: &Proc,
    now: Time,
) -> (results: Vec<ProcessResult>)
    ensures
        results_v(results@) == spec_run_timeout(*config, state@, now),
{
    let mut results = run_timeout_from(config, state, now, 0);
    let ghost queued = results_v(results@);
    let mut rest = derived(config, state, now);
    let ghost rest_v = results_v(rest@);
    results.append(&mut rest);
    proof {
        assert(results_v(results@) =~= queued + rest_v);
    }
    results
}

fn idle(state: &Proc) -> (results: Vec<ProcessResult>)
    ensures
        results_v(results@) == spec_idle(state@),
{
    let mut results: Vec<ProcessResult> = Vec::new();
    results.push(ProcessResult {
        state: copy(state),
        send: Vec::new(),
        marks: Vec::new(),
    });
    proof {
        assert(results_v(results@) =~= spec_idle(state@));
    }
    results
}

impl Proc {
    /// One event at the service: `spec_service`.
    pub fn on_event(
        &self,
        config: &Config,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<ProcessResult>)
        ensures
            results_v(results@) == spec_service(*config, self@, now, *event),
    {
        match event {
            ProcessEvent::Receive { sender: Pid::Outside, message: Message::Request(call) } => {
                run(config, self, call, now)
            }
            ProcessEvent::Timeout => {
                let results = run_timeout(config, self, now);
                if results.is_empty() { idle(self) } else { results }
            }
            _ => idle(self),
        }
    }
}

pub fn initial(_config: &Config) -> (states: Vec<(Pid, Proc)>)
    ensures
        states@.map_values(|entry: (Pid, Proc)| (entry.0, entry.1@))
            == SpecModel.processes(*_config),
        states@.map_values(|entry: (Pid, Proc)| entry.0).no_duplicates(),
        forall|i: int| 0 <= i < states@.len() ==> states@[i].0 != Pid::Outside,
{
        let server = initial_store();
        let pending: Vec<Work> = Vec::new();
        let state = Proc {
            store: server,
            pending,
        };
        proof {
            assert(server@ == empty_store());
            assert(pending@.map_values(|work: Work| crate::projection::as_sched(work)) =~= Seq::empty());
            assert(state@ == SpecProc {
                store: empty_store(),
                pending: Seq::empty(),
            });
        }
        let mut states = Vec::new();
        states.push((Pid::Service, state));
        proof {
            assert(states@.map_values(|entry: (Pid, Proc)| (entry.0, entry.1@))
                =~= seq![(
                    Pid::Service,
                    SpecProc {
                        store: empty_store(),
                        pending: Seq::empty(),
                    },
                )]);
        }
        states
}

pub fn injectable(_config: &Config, message: &Message) -> (injectable: bool)
    ensures
        injectable == SpecModel.injectable(*_config, *message),
{
    match message {
        Message::Request(_) => true,
        Message::Output(_) => false,
    }
}


} // verus!


use echod_abstract_spec::rover as abstract_rover;
use rover_exec as RoverExec;

verus! {

#[derive(Clone, Copy, Debug, Default)]
pub struct Spec;

impl RoverExec::Proc for Proc {
    type Spec = SpecProc;

    fn on_event(
        &self,
        config: &Config,
        now: Time,
        event: &ProcessEvent<Pid, Message>,
    ) -> (results: Vec<RoverExec::ProcResult<Self>>) {
        let mut inner = Proc::on_event(self, config, now, event);
        let ghost all = inner@;
        let mut results: Vec<RoverExec::ProcResult<Proc>> = Vec::new();
        while !inner.is_empty()
            invariant
                results@.len() + inner@.len() == all.len(),
                inner@ == all.skip(results@.len() as int),
                forall|i: int| 0 <= i < results@.len() ==> {
                    let result = #[trigger] results@[i];
                    let source = all[i];
                    &&& result.state@ == source.state@
                    &&& result.send@ == source.send@
                },
            decreases inner.len(),
        {
            let ghost i = results@.len() as int;
            let source = inner.remove(0);
            proof {
                assert(all.skip(i).remove(0) =~= all.skip(i + 1));
            }
            results.push(RoverExec::ProcResult {
                state: source.state,
                send: source.send,
                marks: source.marks,
            });
        }
        results
    }
}

impl RoverExec::Spec for Spec {
    type Spec = abstract_rover::Spec;
    type Proc = Proc;

    open spec fn spec(&self) -> abstract_rover::Spec {
        abstract_rover::Spec
    }

    fn outside(&self) -> Pid {
        Pid::Outside
    }

    fn initial(&self, config: &Config) -> (states: Vec<(Pid, Proc)>) {
        initial(config)
    }

    fn injectable(&self, config: &Config, message: &Message) -> bool {
        injectable(config, message)
    }
}

} // verus!
