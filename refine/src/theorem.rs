//! `concrete_refines_abstract`: every bounded trace of the store machine is
//! a trace of the Resonate model.
//!
//! The relation: the abstract state is the sweep of the concrete one at the
//! clock, translated; the calls in flight are the same; the abstract has sent
//! what the concrete has, plus what that sweep sends; the abstract's pending
//! work is timers, none due, one for every deadline the abstract state owes;
//! the clocks agree; and the concrete side keeps the kernel's invariant, its
//! leases from their ttl, no scoped tag, every version within the wire's.
//!
//! The theorem is `refines_under` from the relation, the initial case and
//! `simulation_holds`: invoke, return and receive are bookkeeping on `rel`; a
//! sweep is a stutter; a tick is `tick::tick_matched`, the model's timers due
//! by the new clock draining to the kernel's sweep there; a request is
//! `effect::effect_matched`, one commutation lemma per handler
//! (`handlers`) and the same drain.

use vstd::prelude::*;

use accordant::refinement::{admits, end, matches, refines_under, shows, simulation_under};
use accordant::semantics::{
    before, effect, initial, invoke, is_first, is_overdue, legal, overdue, project, ready, receive, req_of, ret, run, start_all, step, tick, valid, Cfg, Config, Execution, ExternalOp, Lab, Label,
};
use accordant::{CallId, Event, Model, Sched, Time};
use echod_kernel::properties::inv;
use echod_kernel::steps::{deadline_at, has_deadline, is_next, objects_deadline, strip};
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::twins::*;
use resonate::{Dispatch, Internal, Request, Resonate, Response, Server};

use crate::machine::*;
use crate::sweep::{mdeadline_at, next_deadline, sweep_fn, sweep_sends};
use crate::sweep_proof::{callbacks_spent, lemma_inv_empty, lemma_inv_fresh, lemma_sends_idem, lemma_sweep_idem, lemma_sweep_inv, lemma_sweep_swept, lemma_swept_ahead, listeners_spent, swept};
use crate::frame::{lemma_sweep_shell, no_scope, shell_kept, versions_bounded};
use crate::trans::leases_from_ttl;
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

/// The raw bucket a configuration holds: its outbox emptied, as every step
/// leaves it.
pub open spec fn raw_of(c: Cfg<Concrete>) -> AState {
    fresh(c.state@)
}

/// The abstract state a concrete one stands for at `now`: swept, translated.
pub open spec fn abs(a: AState, now: Time, retry_timeout: u64) -> ServerV {
    translate(sweep_fn(fresh(a), now as nat, retry_timeout as nat))
}

/// The abstract model's pending work, as the relation keeps it: timers only,
/// none due, and one on `id` at `t` for every deadline `t` the abstract
/// state's object `id` owes (the model's deadlines: a pending promise's
/// timeout, whatever its kind; a lease's end; an offer).
pub open spec fn timers_cover(internals: Seq<Sched<Internal>>, a: AState, now: Time) -> bool {
    &&& forall|i: int| 0 <= i < internals.len() ==> match #[trigger] internals[i] {
        Sched::Timer(t, step) => t > now && (step@ matches InternalV::On(ids) && ids.no_duplicates() && ids.len() == 1),
        Sched::Later(_) => false,
    }
    &&& forall|id: Seq<char>, t: nat| #[trigger] a.objects.contains_key(id) && #[trigger] mdeadline_at(a.objects[id], t) ==>
        exists|i: int| 0 <= i < internals.len() && #[trigger] internals[i] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])))
}

/// A timer on `id` at `t` is pending.
pub open spec fn mdeadline_at_timer(internals: Seq<Sched<Internal>>, id: Seq<char>, t: nat) -> bool {
    exists|i: int| 0 <= i < internals.len() && #[trigger] internals[i] == Sched::Timer(t as u64, lift_internal(InternalV::On(seq![id])))
}

/// Some timer is due by `d`.
pub open spec fn timer_by(internals: Seq<Sched<CStep>>, d: nat) -> bool {
    exists|i: int| 0 <= i < internals.len() && match #[trigger] internals[i] {
        Sched::Timer(u, _) => u as nat <= d,
        Sched::Later(_) => false,
    }
}

/// The store machine sweeps before its bucket's next kernel deadline passes:
/// a sweep is armed no later than it. (So the clock never leaves a kernel
/// deadline behind unswept; only internal promises, which the kernel arms
/// no timer for, are read late, and nothing hangs on them.)
pub open spec fn sweep_armed(c: Cfg<Concrete>) -> bool {
    match next_deadline(raw_of(c)) {
        Some(d) => timer_by(c.internals, d),
        None => true,
    }
}

/// Every call in flight is inside the kernel's doors.
pub open spec fn calls_bounded(ext: Map<CallId, ExternalOp<Request, Response>>) -> bool {
    forall|call: CallId| #[trigger] ext.contains_key(call) ==> request_bounded(ext[call].req@)
}

/// The forward simulation relation.
pub open spec fn rel(cfg: Concrete, c: Cfg<Concrete>, s: Cfg<Resonate>) -> bool {
    let raw = raw_of(c);
    let t = cfg.retry_timeout as nat;
    let swept = sweep_fn(raw, c.now as nat, t);
    // the concrete side's own invariants
    &&& c.now <= MAX_TIME
    &&& raw.objects.dom().finite()
    &&& raw.schedules == Map::<Seq<char>, ASchedule>::empty()
    &&& inv(c.now as nat, raw)
    &&& leases_from_ttl(raw)
    &&& no_scope(raw)
    &&& versions_bounded(raw)
    &&& callbacks_spent(raw)
    &&& listeners_spent(raw)
    &&& sweep_armed(c)
    &&& calls_bounded(c.externals)
    // the correspondence
    &&& s.now == c.now
    &&& s.state@ == translate(swept)
    &&& s.externals == c.externals
    &&& (c.sent + lift_dispatches(sweep_sends(raw, c.now as nat, t))).to_multiset().subset_of(s.sent.to_multiset())
    &&& timers_cover(s.internals, swept, c.now)
}

// --------------------------------------------------------------- the lemmas

/// The two machines agree on their one dial; the abstract fires schedules at
/// the instant, which the store machine refuses anyway.
pub open spec fn abstract_of(cfg: Concrete) -> Resonate {
    Resonate { retry_timeout: cfg.retry_timeout, fire_within: 0 }
}

/// The kernel's door on the dial: `Config::wf`.
pub open spec fn dial_ok(cfg: Concrete) -> bool {
    0 < cfg.retry_timeout <= MAX_TIME
}

/// A request inside the kernel's doors: its instants and durations at most
/// `MAX_TIME`, so that no sum the kernel takes wraps where the model's
/// saturates.
pub open spec fn request_bounded(req: RequestV) -> bool {
    well_formed(req) && match req {
        RequestV::CreatePromise(c) => c.timeout_at <= MAX_TIME && (c.tags.delay is Some ==> c.tags.delay.unwrap() <= MAX_TIME),
        RequestV::CreateTask { ttl, action, .. } => ttl <= MAX_TIME && action.timeout_at <= MAX_TIME && (action.tags.delay is Some ==> action.tags.delay.unwrap() <= MAX_TIME),
        RequestV::AcquireTask { ttl, .. } => ttl <= MAX_TIME,
        RequestV::FenceTask { action: FencedV::Create(c), .. } => c.timeout_at <= MAX_TIME && (c.tags.delay is Some ==> c.tags.delay.unwrap() <= MAX_TIME),
        RequestV::CreateSchedule(_) | RequestV::GetSchedule(_) | RequestV::DeleteSchedule(_) => false,
        _ => true,
    }
}

/// The labels the theorem is about: the clock stays within the kernel's door
/// and every request does; silence and the rest are admitted.
pub open spec fn bounded(l: Lab<Concrete>) -> bool {
    match l {
        Label::Obs(Event::Clock { at }) => at <= MAX_TIME,
        Label::Obs(Event::Invoke { req, .. }) => request_bounded(req@),
        _ => true,
    }
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
    broadcast use vstd::multiset::group_multiset_axioms;
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let c = initial::<Concrete>(lift_store(concrete_init()));
    let s = initial::<Resonate>(abstract_init());
    axiom_store_realised(concrete_init());
    axiom_realised(empty_v(), ResponseV::Status(0), InternalV::On(Seq::empty()), DispatchV::Execute { id: Seq::empty(), version: 0 });
    let raw = raw_of(c);
    assert(raw == concrete_init());
    let swept = sweep_fn(raw, 0, cfg.retry_timeout as nat);
    lemma_sweep_empty(cfg.retry_timeout as nat);
    assert(swept == concrete_init());
    assert(raw.objects.dom() =~= Set::<Seq<char>>::empty());
    assert(translate(swept).promises =~= Map::<Seq<char>, PromiseV>::empty());
    assert(translate(swept).tasks =~= Map::<Seq<char>, TaskV>::empty());
    assert(s.state@.promises =~= Map::<Seq<char>, PromiseV>::empty());
    assert(s.state@.tasks =~= Map::<Seq<char>, TaskV>::empty());
    assert(s.state@.schedules =~= Map::<Seq<char>, ScheduleV>::empty());
    lemma_inv_empty(0);
    assert(sweep_armed(c)) by {
        if next_deadline(raw) is Some {
            let d = choose|t: nat| is_next(strip(raw), t);
            assert(has_deadline(strip(raw), d));
            assert(false);
        }
    }
    lemma_sends_idem(raw, 0, cfg.retry_timeout as nat);
    assert(c.sent + lift_dispatches(sweep_sends(raw, 0, cfg.retry_timeout as nat)) =~= Seq::<Dispatch>::empty());
    assert forall|id: Seq<char>, t: nat| #[trigger] swept.objects.contains_key(id) && #[trigger] mdeadline_at(swept.objects[id], t) implies false by {}
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
        bounded(l),
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
            assert(calls_bounded(y.externals)) by {
                assert forall|k: CallId| #[trigger] y.externals.contains_key(k) implies request_bounded(y.externals[k].req@) by {
                    if k != call {
                        assert(x.externals.contains_key(k));
                    }
                }
            }
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
            let raw = raw_of(x);
            let extra = lift_dispatches(sweep_sends(raw, x.now as nat, cfg.retry_timeout as nat));
            let i = choose|i: int| 0 <= i < x.sent.len() && #[trigger] x.sent[i] == msg && y == Config { sent: x.sent.remove(i), ..x };
            // the message is among the abstract's sent
            assert(x.sent.contains(msg));
            assert((x.sent + extra).contains(msg)) by {
                assert((x.sent + extra)[i] == msg);
            }
            let m1 = (x.sent + extra).to_multiset();
            let m2 = s.sent.to_multiset();
            assert(m1.count(msg) > 0);
            assert(m2.count(msg) > 0);
            assert(s.sent.contains(msg));
            let j = choose|j: int| 0 <= j < s.sent.len() && #[trigger] s.sent[j] == msg;
            let t = Config { sent: s.sent.remove(j), ..s };
            no_overdue(cfg, x, s);
            assert(receive(a, s, l, t)) by {
                assert(0 <= j < s.sent.len() && s.sent[j] == msg && t == Config { sent: s.sent.remove(j), ..s });
            }
            one_step(a, s, l, t);
            // what is left: one of this message fewer on each side
            assert(t.sent.to_multiset() == m2.remove(msg));
            assert(y.sent.to_multiset() == x.sent.to_multiset().remove(msg));
            assert((y.sent + extra).to_multiset() =~= m1.remove(msg));
            assert(m1.remove(msg).subset_of(m2.remove(msg))) by {
                assert forall|v: Dispatch| m1.remove(msg).count(v) <= m2.remove(msg).count(v) by {
                    assert(m1.count(v) <= m2.count(v));
                }
            }
            assert(rel(cfg, y, t));
        },
        _ => {
            assert(false);
        },
    }
}

/// The clock moves: the model ticks and drains to the sweep at the new
/// instant (`tick::tick_matched`).
pub proof fn matched_tick(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        dial_ok(cfg),
        bounded(l),
        rel(cfg, x, s),
        tick(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    crate::tick::tick_matched(cfg, x, l, y, s);
}

/// A request takes effect: the kernel's handler after a sweep against the
/// model's twin on the translated state (`effect::effect_matched`), one
/// lemma per handler (`handlers`).
pub proof fn matched_effect(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        dial_ok(cfg),
        bounded(l),
        rel(cfg, x, s),
        effect(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    crate::effect::effect_matched(cfg, x, l, y, s);
}

/// A concrete sweep runs: a stutter. The relation reads the concrete state
/// swept already, and sweeping a swept state changes nothing and sends
/// nothing (`lemma_sweep_idem`, `lemma_sends_idem`, with `lemma_sweep_swept`
/// for the state the sweep leaves).
pub proof fn matched_run(cfg: Concrete, x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>)
    requires
        dial_ok(cfg),
        rel(cfg, x, s),
        run(cfg, x, l, y),
    ensures
        exists|t: Cfg<Resonate>| #[trigger] matches(abstract_of(cfg), s, l, t) && rel(cfg, y, t),
{
    broadcast use vstd::seq_lib::lemma_multiset_commutative;
    broadcast use vstd::multiset::group_multiset_axioms;
    let a = abstract_of(cfg);
    let t = cfg.retry_timeout as nat;
    let now = x.now as nat;
    // the concrete step: the one outcome of the one kind of internal work
    let (i, j) = choose|i: int, j: int|
        #![trigger x.internals[i], cfg.spec_internal(req_of(x.internals[i]), x.state, x.now)[j]]
        0 <= i < x.internals.len() && ready(x.now, x.internals[i]) && (overdue(cfg, x) ==> is_first(cfg, x, i)) && {
            let outs = cfg.spec_internal(req_of(x.internals[i]), x.state, x.now);
            0 <= j < outs.len() && y == Config {
                state: outs[j].next,
                internals: start_all(x.internals.remove(i), outs[j].work, x.now),
                sent: x.sent + outs[j].send,
                ..x
            }
        };
    let raw = raw_of(x);
    let sw = sweep_fn(raw, now, t);
    let emitted = sweep_sends(raw, now, t);
    assert(y.state == lift_store(fresh(sw)));
    assert(y.sent == x.sent + lift_dispatches(emitted));
    assert(y.internals == start_all(x.internals.remove(i), arm(sw), x.now));
    assert(y.now == x.now && y.externals == x.externals);
    axiom_store_realised(fresh(sw));
    assert(y.state@ == fresh(sw));
    let raw2 = raw_of(y);
    assert(raw2 == fresh(sw));
    // the state the sweep leaves is swept: sweeping it again is the identity
    lemma_sweep_swept(raw, now, t);
    assert(swept(fresh(sw), now));
    lemma_sweep_idem(raw2, now, t);
    lemma_sends_idem(raw2, now, t);
    let sw2 = sweep_fn(raw2, now, t);
    assert(sw2 == raw2);
    assert(lift_dispatches(sweep_sends(raw2, now, t)) =~= Seq::<Dispatch>::empty());
    assert(y.sent + lift_dispatches(sweep_sends(raw2, now, t)) =~= y.sent);
    // the concrete side's invariants carry over
    lemma_sweep_inv(raw, now, t);
    lemma_inv_fresh(now, sw);
    assert(inv(now, raw2));
    crate::tick::lemma_sweep_leases(raw, now, t);
    assert(leases_from_ttl(raw2));
    lemma_sweep_shell(raw, now, t);
    assert(shell_kept(raw, raw2));
    crate::frame::lemma_shell_keeps(raw, raw2);
    assert(no_scope(raw2) && versions_bounded(raw2));
    assert(raw2.objects.dom() =~= raw.objects.dom());
    assert(sweep_armed(y)) by {
        match next_deadline(raw2) {
            Some(d) => {
                assert(strip(raw2) == strip(sw));
                assert(is_next(strip(sw), d));
                assert(has_deadline(strip(sw), d));
                assert(objects_deadline(sw.objects, d));
                let id = choose|id: Seq<char>| #[trigger] sw.objects.contains_key(id) && deadline_at(sw.objects[id], d);
                lemma_swept_ahead(sw, now);
                assert(d > now);
                assert(d <= u64::MAX);
                assert(arm(sw) == seq![Sched::Timer(d as u64, CStep::Sweep)]);
                let n = x.internals.remove(i).len();
                assert(y.internals.len() == n + 1);
                assert(y.internals[n as int] == Sched::Timer(d as u64, CStep::Sweep));
                assert(timer_by(y.internals, d));
            },
            None => {},
        }
    }
    // the abstract side stands still
    let mid: Execution<Resonate> = Seq::empty();
    assert(legal(a, s, mid));
    assert(project::<Resonate>(mid) =~= shows(l));
    assert(end::<Resonate>(s, mid) == s);
    assert(matches(a, s, l, s));
    // and stays related: same translation, same messages, same deadlines
    assert(translate(sw2) == translate(sw));
    assert((y.sent + lift_dispatches(sweep_sends(raw2, now, t))).to_multiset() == (x.sent + lift_dispatches(emitted)).to_multiset());
    assert(timers_cover(s.internals, sw2, y.now));
    assert(rel(cfg, y, s));
}

/// Every bounded concrete step from related configurations is matched by the
/// abstract model: by the kind of the step.
pub proof fn simulation_holds(cfg: Concrete)
    requires
        dial_ok(cfg),
    ensures
        simulation_under(cfg, abstract_of(cfg), |c: Cfg<Concrete>, s: Cfg<Resonate>| rel(cfg, c, s), |l: Lab<Concrete>| bounded(l)),
{
    let a = abstract_of(cfg);
    let r = |c: Cfg<Concrete>, s: Cfg<Resonate>| rel(cfg, c, s);
    let ok = |l: Lab<Concrete>| bounded(l);
    assert forall|x: Cfg<Concrete>, l: Lab<Concrete>, y: Cfg<Concrete>, s: Cfg<Resonate>| #![trigger r(x, s), step(cfg, x, l, y)]
        r(x, s) && step(cfg, x, l, y) && ok(l) implies exists|t: Cfg<Resonate>| #[trigger] matches(a, s, l, t) && r(y, t) by {
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

/// Every trace the store machine can show a client, within the kernel's
/// doors (the clock and every request's instants and durations at most
/// `MAX_TIME`), the Resonate model can show.
pub proof fn concrete_refines_abstract(cfg: Concrete, trace: Seq<Event<Request, Response, Dispatch>>)
    requires
        dial_ok(cfg),
        admits(|l: Lab<Concrete>| bounded(l), trace),
        valid(cfg, lift_store(concrete_init()), trace),
    ensures
        valid(abstract_of(cfg), abstract_init(), trace),
{
    let r = |c: Cfg<Concrete>, s: Cfg<Resonate>| rel(cfg, c, s);
    let ok = |l: Lab<Concrete>| bounded(l);
    init_related(cfg);
    simulation_holds(cfg);
    refines_under(cfg, abstract_of(cfg), r, ok, lift_store(concrete_init()), abstract_init(), trace);
}

} // verus!
