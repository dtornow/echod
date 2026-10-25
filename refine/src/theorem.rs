//! `concrete_refines_abstract`: every trace of the store machine is a trace of
//! the Resonate model.
//!
//! The relation: the abstract state is the sweep of the concrete one at the
//! clock, translated; the calls in flight are the same; the abstract has sent
//! what the concrete has, plus what that sweep sends; the abstract's pending
//! work is timers, none due, one for every deadline the abstract state owes;
//! the clocks agree.
//!
//! What is proved here: the theorem from the relation and the simulation, by
//! `accordant::refinement::refines`; the initial configurations are related.
//! What is not: `simulation_holds`, that every concrete step from related
//! configurations is matched. It is stated with `admit()`, so this crate
//! verifies with one hole, named. Filling it is the per-step work: invoke,
//! return and receive are bookkeeping on `rel`; a tick is the lemma that the
//! sweep at the new clock is what the abstract timers due by then compute; a
//! request is one commutation lemma per handler, the kernel's `spec_handle`
//! after a sweep against the model's twin on the translated state.

use vstd::prelude::*;

use accordant::refinement::{refines, simulation};
use accordant::semantics::{initial, valid, Cfg, Config, ExternalOp};
use accordant::{Event, Sched, Time};
use echod_kernel::steps::{deadline_at, strip};
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::twins::*;
use resonate::{Dispatch, Internal, Request, Resonate, Response, Server};

use crate::machine::*;
use crate::sweep::sweep_fn;
use crate::translate::*;

verus! {

// --------------------------------------------------------------- the relation

/// The kernel's task as the model's: the lease's start recovered from its end.
pub open spec fn task_v(t: ATask) -> TaskV {
    TaskV {
        state: tstate_out(t.state),
        version: t.version as u32,
        pid: t.pid,
        ttl: t.ttl,
        acquired_at: match (t.lease_timeout_at, t.ttl) {
            (Some(end), Some(ttl)) => if end >= ttl { (end - ttl) as u64 } else { 0 },
            _ => 0,
        },
        retry_at: t.retry_timeout_at,
        resumes: t.resumes,
    }
}

/// The kernel's object as the model's promise.
pub open spec fn promise_v(p: APromise) -> PromiseV {
    PromiseV {
        state: pstate_out(p.state),
        value: value_out(p.value),
        param: value_out(p.param),
        timeout_at: p.timeout_at,
        created_at: p.created_at,
        settled_at: p.settled_at,
        tags: tags_out(p.tags),
        callbacks: p.callbacks.to_set(),
        listeners: p.listeners.to_set(),
    }
}

/// The kernel's state as the model's: every object a promise, every object
/// with a task a task; no schedules.
pub open spec fn translate(a: AState) -> ServerV {
    ServerV {
        promises: a.objects.map_values(|p: APromise| promise_v(p)),
        tasks: Map::new(
            a.objects.dom().filter(|k: Seq<char>| a.objects[k].task is Some),
            |k: Seq<char>| task_v(a.objects[k].task.unwrap()),
        ),
        schedules: Map::empty(),
    }
}

/// The abstract state a concrete one stands for at `now`: swept, translated.
pub open spec fn abs(a: AState, now: Time, retry_timeout: u64) -> ServerV {
    translate(sweep_fn(fresh(a), now as nat, retry_timeout as nat))
}

/// The abstract model's pending work, as the relation keeps it: timers only,
/// none due, and one on `id` at `t` for every deadline `t` the abstract state's
/// object `id` owes.
pub open spec fn timers_cover(internals: Seq<Sched<Internal>>, a: AState, now: Time) -> bool {
    &&& forall|i: int| 0 <= i < internals.len() ==> match #[trigger] internals[i] {
        Sched::Timer(t, step) => t > now && (step@ matches InternalV::On(_)),
        Sched::Later(_) => false,
    }
    &&& forall|id: Seq<char>, t: nat| #[trigger] a.objects.contains_key(id) && #[trigger] deadline_at(a.objects[id], t) ==>
        exists|i: int| 0 <= i < internals.len() && #[trigger] internals[i] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])))
}

/// The forward simulation relation.
pub open spec fn rel(cfg: Concrete, c: Cfg<Concrete>, s: Cfg<Resonate>) -> bool {
    let swept = sweep_fn(fresh(c.state@), c.now as nat, cfg.retry_timeout as nat);
    &&& s.now == c.now
    &&& s.state@ == translate(swept)
    &&& s.externals == c.externals
    &&& s.sent.to_multiset() == (c.sent + lift_dispatches(sends(swept))).to_multiset()
    &&& timers_cover(s.internals, swept, c.now)
}

// --------------------------------------------------------------- the lemmas

/// The two machines agree on their one dial; the abstract fires schedules at
/// the instant, which the store machine refuses anyway.
pub open spec fn abstract_of(cfg: Concrete) -> Resonate {
    Resonate { retry_timeout: cfg.retry_timeout, fire_within: 0 }
}

/// The empty server, as the model's value with that view.
pub open spec fn empty_v() -> ServerV {
    ServerV { promises: Map::empty(), tasks: Map::empty(), schedules: Map::empty() }
}

pub open spec fn abstract_init() -> Server {
    lift_server(empty_v())
}

/// The empty bucket stands for the empty server.
pub proof fn init_related(cfg: Concrete)
    ensures
        rel(cfg, initial::<Concrete>(lift_store(concrete_init())), initial::<Resonate>(abstract_init())),
{
    let c = initial::<Concrete>(lift_store(concrete_init()));
    let s = initial::<Resonate>(abstract_init());
    axiom_store_realised(concrete_init());
    axiom_realised(empty_v(), ResponseV::Status(0), InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    let swept = sweep_fn(fresh(c.state@), 0, cfg.retry_timeout as nat);
    lemma_sweep_empty(cfg.retry_timeout as nat);
    assert(swept == concrete_init());
    assert(translate(swept).promises =~= Map::<Seq<char>, PromiseV>::empty());
    assert(translate(swept).tasks =~= Map::<Seq<char>, TaskV>::empty());
    assert(s.state@.promises =~= Map::<Seq<char>, PromiseV>::empty());
    assert(s.state@.tasks =~= Map::<Seq<char>, TaskV>::empty());
    assert(s.state@.schedules =~= Map::<Seq<char>, ScheduleV>::empty());
    assert(sends(swept) =~= Seq::<DispatchV>::empty());
    assert(c.sent + lift_dispatches(sends(swept)) =~= Seq::<Dispatch>::empty());
    assert forall|id: Seq<char>, t: nat| #[trigger] swept.objects.contains_key(id) && #[trigger] deadline_at(swept.objects[id], t) implies false by {}
}

/// Sweeping the empty bucket leaves it empty.
pub proof fn lemma_sweep_empty(retry_timeout: nat)
    ensures
        sweep_fn(fresh(concrete_init()), 0, retry_timeout) == concrete_init(),
{
    let a = fresh(concrete_init());
    assert(a == concrete_init());
    assert(a.objects.dom() =~= Set::<Seq<char>>::empty());
    vstd::set_lib::lemma_set_empty_equivalency_len::<Seq<char>>(a.objects.dom());
    assert(crate::sweep::ids_of(a).len() == 0);
    assert(crate::sweep::ids_of(a) =~= Seq::<Seq<char>>::empty());
}

/// ADMITTED. Every concrete step from related configurations is matched by
/// the abstract model: the content of the refinement, step kind by step kind
/// and handler by handler.
pub proof fn simulation_holds(cfg: Concrete)
    ensures
        simulation(cfg, abstract_of(cfg), |c: Cfg<Concrete>, s: Cfg<Resonate>| rel(cfg, c, s)),
{
    admit();
}

// --------------------------------------------------------------- the theorem

/// Every trace the store machine can show a client, the Resonate model can.
pub proof fn concrete_refines_abstract(cfg: Concrete, trace: Seq<Event<Request, Response, Dispatch>>)
    requires
        valid(cfg, lift_store(concrete_init()), trace),
    ensures
        valid(abstract_of(cfg), abstract_init(), trace),
{
    let r = |c: Cfg<Concrete>, s: Cfg<Resonate>| rel(cfg, c, s);
    init_related(cfg);
    simulation_holds(cfg);
    refines(cfg, abstract_of(cfg), r, lift_store(concrete_init()), abstract_init(), trace);
}

} // verus!
