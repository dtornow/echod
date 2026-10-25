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

use accordant::refinement::{end, matches, refines, shows, simulation};
use accordant::semantics::{
    before, effect, initial, invoke, is_overdue, legal, overdue, project, receive, ret, run, step, tick, valid, Cfg, Config, Execution, ExternalOp, Lab, Label,
};
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

// ------------------------------------------------------------ the step cases

/// No abstract timer is due: the relation keeps them all ahead of the clock.
pub proof fn no_overdue(cfg: Concrete, x: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        rel(cfg, x, s),
    ensures
        !overdue(abstract_of(cfg), s),
{
    let a = abstract_of(cfg);
    assert forall|i: int| !is_overdue(a, s, i) by {
        if 0 <= i < s.internals.len() {
            match s.internals[i] {
                Sched::Timer(t, _) => {
                    assert(t > x.now);
                }
                Sched::Later(_) => {}
            }
        }
    }
}

/// A run of one step, from `s` to `t`, shows what it shows.
pub proof fn one_step(a: Resonate, s: Cfg<Resonate>, l: Lab<Resonate>, t: Cfg<Resonate>)
    requires
        step(a, s, l, t),
    ensures
        matches(a, s, l, t),
{
    let mid: Execution<Resonate> = seq![(l, t)];
    assert(legal(a, s, mid)) by {
        assert forall|i: int| 0 <= i < mid.len() implies #[trigger] step(a, before::<Resonate>(s, mid, i), mid[i].0, mid[i].1) by {
            assert(i == 0);
            assert(before::<Resonate>(s, mid, 0) == s);
        }
    }
    assert(mid.drop_last() =~= Seq::<(Lab<Resonate>, Cfg<Resonate>)>::empty());
    assert(mid.last() == (l, t));
    assert(project::<Resonate>(mid.drop_last()) =~= Seq::<Event<Request, Response, Dispatch>>::empty());
    match l {
        Label::Obs(e) => {
            assert(project::<Resonate>(mid) =~= Seq::<Event<Request, Response, Dispatch>>::empty().push(e));
            assert(shows(l) =~= Seq::<Event<Request, Response, Dispatch>>::empty().push(e));
        },
        Label::Silent => {
            assert(project::<Resonate>(mid) =~= Seq::<Event<Request, Response, Dispatch>>::empty());
            assert(shows(l) =~= Seq::<Event<Request, Response, Dispatch>>::empty());
        },
    }
    assert(end::<Resonate>(s, mid) == t);
}

/// A client sends a request: the same step on both sides.
pub proof fn matched_invoke(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        rel(cfg, x, s),
        invoke(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    let a = abstract_of(cfg);
    match l {
        Label::Obs(Event::Invoke { call, req }) => {
            let t = Config { externals: s.externals.insert(call, ExternalOp { req, res: None }), ..s };
            no_overdue(cfg, x, s);
            assert(invoke(a, s, l, t));
            one_step(a, s, l, t);
            assert(rel(cfg, y, t));
        },
        _ => {
            assert(false);
        },
    }
}

/// A client receives its response: the same step on both sides.
pub proof fn matched_ret(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        rel(cfg, x, s),
        ret(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    let a = abstract_of(cfg);
    match l {
        Label::Obs(Event::Return { call, res }) => {
            let t = Config { externals: s.externals.remove(call), ..s };
            no_overdue(cfg, x, s);
            assert(ret(a, s, l, t));
            one_step(a, s, l, t);
            assert(rel(cfg, y, t));
        },
        _ => {
            assert(false);
        },
    }
}

/// A client receives a dispatch: the abstract side holds every message the
/// concrete side has sent, so it has this one too.
pub proof fn matched_receive(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        rel(cfg, x, s),
        receive(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::seq_lib::to_multiset_remove;
    broadcast use vstd::seq_lib::to_multiset_contains;
    broadcast use vstd::multiset::group_multiset_axioms;
    let a = abstract_of(cfg);
    match l {
        Label::Obs(Event::Receive { msg }) => {
            let swept = sweep_fn(fresh(x.state@), x.now as nat, cfg.retry_timeout as nat);
            let extra = lift_dispatches(sends(swept));
            let i = choose|i: int| 0 <= i < x.sent.len() && #[trigger] x.sent[i] == msg && y == Config { sent: x.sent.remove(i), ..x };
            // the message is among the abstract's sent
            assert(x.sent.contains(msg));
            assert((x.sent + extra).contains(msg)) by {
                assert((x.sent + extra)[i] == msg);
            }
            assert((x.sent + extra).to_multiset().count(msg) > 0);
            assert(s.sent.to_multiset().count(msg) > 0);
            assert(s.sent.contains(msg));
            let j = choose|j: int| 0 <= j < s.sent.len() && #[trigger] s.sent[j] == msg;
            let t = Config { sent: s.sent.remove(j), ..s };
            no_overdue(cfg, x, s);
            assert(receive(a, s, l, t)) by {
                assert(0 <= j < s.sent.len() && s.sent[j] == msg && t == Config { sent: s.sent.remove(j), ..s });
            }
            one_step(a, s, l, t);
            // what is left: the same multiset, less one of this message
            assert(t.sent.to_multiset() == s.sent.to_multiset().remove(msg));
            assert(y.sent.to_multiset() == x.sent.to_multiset().remove(msg));
            assert((y.sent + extra).to_multiset() =~= (x.sent + extra).to_multiset().remove(msg));
            assert(rel(cfg, y, t));
        },
        _ => {
            assert(false);
        },
    }
}

/// ADMITTED. The clock moves: the abstract timers due by the new instant run,
/// in deadline order, and compute the sweep at that instant.
pub proof fn matched_tick(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        rel(cfg, x, s),
        tick(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    admit();
}

/// ADMITTED. A request takes effect: the kernel's handler after a sweep
/// against the model's twin on the translated state, one lemma per handler.
pub proof fn matched_effect(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        rel(cfg, x, s),
        effect(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    admit();
}

/// ADMITTED. A concrete sweep runs: a stutter, since the relation already
/// reads the concrete state swept; needs the sweep idempotent.
pub proof fn matched_run(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        rel(cfg, x, s),
        run(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    admit();
}

/// Every concrete step from related configurations is matched by the abstract
/// model: by the kind of the step.
pub proof fn simulation_holds(cfg: Concrete)
    ensures
        simulation(cfg, abstract_of(cfg), |c: Cfg<Concrete>, s: Cfg<Resonate>| rel(cfg, c, s)),
{
    let a = abstract_of(cfg);
    let r = |c: Cfg<Concrete>, s: Cfg<Resonate>| rel(cfg, c, s);
    assert forall|x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>| #![trigger r(x, s), step(cfg, x, l, y)]
        r(x, s) && step(cfg, x, l, y) implies exists|t: Cfg<Resonate>| #[trigger] matches(a, s, l, t) && r(y, t) by {
        if invoke(cfg, x, l, y) {
            matched_invoke(cfg, x, l, y, s);
        } else if ret(cfg, x, l, y) {
            matched_ret(cfg, x, l, y, s);
        } else if receive(cfg, x, l, y) {
            matched_receive(cfg, x, l, y, s);
        } else if tick(cfg, x, l, y) {
            matched_tick(cfg, x, l, y, s);
        } else if effect(cfg, x, l, y) {
            matched_effect(cfg, x, l, y, s);
        } else {
            assert(run(cfg, x, l, y));
            matched_run(cfg, x, l, y, s);
        }
        let t = choose|t: Cfg<Resonate>| #[trigger] matches(a, s, l, t) && rel(cfg, y, t);
        assert(r(y, t));
    }
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
