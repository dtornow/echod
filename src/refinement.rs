//! Trace inclusion between two models, by forward simulation.
//!
//! Two models with the same request, response and dispatch types show
//! clients the same kind of trace. `refines` says: every trace one model can
//! show (`valid`, `semantics.rs`), the other can show too. The proof is the
//! usual one: a relation between configurations that holds initially and is
//! kept by every step, each concrete step matched by a run of abstract steps
//! that shows the same event (one observation, or nothing). Specification and
//! proof only; nothing here runs.

use vstd::prelude::*;

use crate::semantics::*;
use crate::{Event, Model};

verus! {

/// What a run of steps shows: `l`'s event, or nothing.
pub open spec fn shows<X, R, D>(l: Label<X, R, D>) -> Seq<Event<X, R, D>> {
    match l {
        Label::Obs(e) => seq![e],
        Label::Silent => Seq::empty(),
    }
}

/// Where an execution from `first` ends: `first` itself when it is empty.
pub open spec fn end<M: Model>(first: Cfg<M>, steps: Execution<M>) -> Cfg<M> {
    if steps.len() == 0 { first } else { steps.last().1 }
}

/// Abstract model `a` matches one concrete step labeled `l` from `s`: a legal
/// run from `s` that shows exactly what `l` shows and ends in `t`. Empty when
/// the concrete step is a stutter.
pub open spec fn matches<X, R, D, A: Model<External = X, Response = R, Dispatch = D>>(
    a: A, s: Cfg<A>, l: Label<X, R, D>, t: Cfg<A>,
) -> bool {
    exists|mid: Execution<A>| #![trigger legal(a, s, mid)]
        legal(a, s, mid) && project::<A>(mid) == shows(l) && end::<A>(s, mid) == t
}

/// `r` is a forward simulation from concrete `c` to abstract `a`, for steps
/// whose labels `ok` admits: every such concrete step from a related
/// configuration is matched by abstract steps that lead to a related one.
pub open spec fn simulation_under<X, R, D, C: Model<External = X, Response = R, Dispatch = D>, A: Model<External = X, Response = R, Dispatch = D>>(
    c: C, a: A, r: spec_fn(Cfg<C>, Cfg<A>) -> bool, ok: spec_fn(Label<X, R, D>) -> bool,
) -> bool {
    forall|x: Cfg<C>, l: Label<X, R, D>, y: Cfg<C>, s: Cfg<A>| #![trigger r(x, s), step(c, x, l, y)]
        r(x, s) && step(c, x, l, y) && ok(l) ==> exists|t: Cfg<A>| #[trigger] matches(a, s, l, t) && r(y, t)
}

/// A forward simulation for every step.
pub open spec fn simulation<X, R, D, C: Model<External = X, Response = R, Dispatch = D>, A: Model<External = X, Response = R, Dispatch = D>>(
    c: C, a: A, r: spec_fn(Cfg<C>, Cfg<A>) -> bool,
) -> bool {
    simulation_under(c, a, r, |l: Label<X, R, D>| true)
}

/// Every label of an execution that shows `trace` is admitted by `ok`: its
/// observed events are the trace's, and `ok` admits silence.
pub open spec fn admits<X, R, D>(ok: spec_fn(Label<X, R, D>) -> bool, trace: Seq<Event<X, R, D>>) -> bool {
    ok(Label::Silent) && forall|i: int| 0 <= i < trace.len() ==> #[trigger] ok(Label::Obs(trace[i]))
}

// ------------------------------------------------------------- executions

/// `project` distributes over concatenation.
pub proof fn lemma_project_add<M: Model>(s1: Execution<M>, s2: Execution<M>)
    ensures project::<M>(s1 + s2) == project::<M>(s1) + project::<M>(s2),
    decreases s2.len(),
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
        assert(project::<M>(s2) =~= Seq::empty());
        assert(project::<M>(s1) + project::<M>(s2) =~= project::<M>(s1));
    } else {
        lemma_project_add::<M>(s1, s2.drop_last());
        assert((s1 + s2).drop_last() =~= s1 + s2.drop_last());
        assert((s1 + s2).last() == s2.last());
        match s2.last().0 {
            Label::Obs(e) => {
                assert(project::<M>(s1 + s2) =~= project::<M>(s1) + project::<M>(s2));
            }
            Label::Silent => {
                assert(project::<M>(s1 + s2) =~= project::<M>(s1) + project::<M>(s2));
            }
        }
    }
}

/// A legal execution followed by a legal one from where it ends is legal.
pub proof fn lemma_legal_add<M: Model>(m: M, first: Cfg<M>, s1: Execution<M>, s2: Execution<M>)
    requires
        legal(m, first, s1),
        legal(m, end::<M>(first, s1), s2),
    ensures
        legal(m, first, s1 + s2),
{
    let s = s1 + s2;
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] step(m, before::<M>(first, s, i), s[i].0, s[i].1) by {
        if i < s1.len() {
            assert(before::<M>(first, s, i) == before::<M>(first, s1, i));
            assert(s[i] == s1[i]);
        } else {
            let k = i - s1.len();
            assert(s[i] == s2[k]);
            if k == 0 {
                assert(before::<M>(first, s, i) == end::<M>(first, s1));
            } else {
                assert(before::<M>(first, s, i) == s2[k - 1].1);
            }
            assert(before::<M>(first, s, i) == before::<M>(end::<M>(first, s1), s2, k));
        }
    }
}

/// Where a concatenation ends.
pub proof fn lemma_end_add<M: Model>(first: Cfg<M>, s1: Execution<M>, s2: Execution<M>)
    ensures end::<M>(first, s1 + s2) == end::<M>(end::<M>(first, s1), s2),
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        assert((s1 + s2).last() == s2.last());
    }
}

// --------------------------------------------------------------- the theorem

/// Every label of a legal execution showing `trace` is admitted, when `ok`
/// admits the trace: a step's label is silent or one of the trace's events.
proof fn lemma_labels_admitted<X, R, D, C: Model<External = X, Response = R, Dispatch = D>>(
    ok: spec_fn(Label<X, R, D>) -> bool, trace: Seq<Event<X, R, D>>, steps: Execution<C>, k: int,
)
    requires
        admits(ok, trace),
        project::<C>(steps) == trace,
        0 <= k < steps.len(),
    ensures
        ok(steps[k].0),
{
    match steps[k].0 {
        Label::Silent => {}
        Label::Obs(e) => {
            // the event is the trace's: project keeps every observed label, in order
            lemma_project_add::<C>(steps.take(k + 1), steps.skip(k + 1));
            assert(steps.take(k + 1) + steps.skip(k + 1) =~= steps);
            lemma_project_add::<C>(steps.take(k), seq![steps[k]]);
            assert(steps.take(k) + seq![steps[k]] =~= steps.take(k + 1));
            let one: Execution<C> = seq![steps[k]];
            assert(one.drop_last() =~= Seq::<(Lab<C>, Cfg<C>)>::empty());
            assert(one.last() == steps[k]);
            assert(project::<C>(one.drop_last()) =~= Seq::<Event<X, R, D>>::empty());
            assert(project::<C>(one) =~= Seq::<Event<X, R, D>>::empty().push(e));
            assert(project::<C>(one) =~= seq![e]);
            let j = project::<C>(steps.take(k)).len() as int;
            assert(project::<C>(steps.take(k + 1)) =~= project::<C>(steps.take(k)).push(e));
            assert(trace[j] == e);
            assert(0 <= j < trace.len());
        }
    }
}

/// The first `k` concrete steps are matched: some abstract execution from
/// `initial(ai)` shows what they show and ends related to where they end.
proof fn lemma_simulate<X, R, D, C: Model<External = X, Response = R, Dispatch = D>, A: Model<External = X, Response = R, Dispatch = D>>(
    c: C, a: A, r: spec_fn(Cfg<C>, Cfg<A>) -> bool, ok: spec_fn(Label<X, R, D>) -> bool, ci: C::State, ai: A::State, steps: Execution<C>, k: int,
)
    requires
        r(initial::<C>(ci), initial::<A>(ai)),
        simulation_under(c, a, r, ok),
        legal(c, initial::<C>(ci), steps),
        forall|i: int| 0 <= i < steps.len() ==> #[trigger] ok(steps[i].0),
        0 <= k <= steps.len(),
    ensures
        exists|asteps: Execution<A>| #![trigger legal(a, initial::<A>(ai), asteps)]
            legal(a, initial::<A>(ai), asteps)
            && project::<A>(asteps) == project::<C>(steps.take(k))
            && r(before::<C>(initial::<C>(ci), steps, k), end::<A>(initial::<A>(ai), asteps)),
    decreases k,
{
    let first = initial::<C>(ci);
    let afirst = initial::<A>(ai);
    if k == 0 {
        let asteps: Execution<A> = Seq::empty();
        assert(steps.take(0) =~= Seq::<(Lab<C>, Cfg<C>)>::empty());
        assert(project::<A>(asteps) =~= project::<C>(steps.take(0)));
        assert(legal(a, afirst, asteps));
    } else {
        lemma_simulate(c, a, r, ok, ci, ai, steps, k - 1);
        let asteps = choose|asteps: Execution<A>| #![trigger legal(a, afirst, asteps)]
            legal(a, afirst, asteps)
            && project::<A>(asteps) == project::<C>(steps.take(k - 1))
            && r(before::<C>(first, steps, k - 1), end::<A>(afirst, asteps));
        let x = before::<C>(first, steps, k - 1);
        let l = steps[k - 1].0;
        let y = steps[k - 1].1;
        let s = end::<A>(afirst, asteps);
        assert(step(c, x, l, y));
        assert(ok(l));
        let t = choose|t: Cfg<A>| #[trigger] matches(a, s, l, t) && r(y, t);
        let mid = choose|mid: Execution<A>| #![trigger legal(a, s, mid)]
            legal(a, s, mid) && project::<A>(mid) == shows(l) && end::<A>(s, mid) == t;
        let all = asteps + mid;
        lemma_legal_add(a, afirst, asteps, mid);
        lemma_project_add::<A>(asteps, mid);
        lemma_end_add::<A>(afirst, asteps, mid);
        // what the first k concrete steps show: the first k-1, then the k-th
        assert(steps.take(k).drop_last() =~= steps.take(k - 1));
        assert(steps.take(k).last() == steps[k - 1]);
        match l {
            Label::Obs(e) => {
                assert(project::<C>(steps.take(k)) =~= project::<C>(steps.take(k - 1)).push(e));
                assert(shows(l) =~= seq![e]);
                assert(project::<A>(all) =~= project::<C>(steps.take(k)));
            }
            Label::Silent => {
                assert(project::<C>(steps.take(k)) =~= project::<C>(steps.take(k - 1)));
                assert(project::<A>(all) =~= project::<C>(steps.take(k)));
            }
        }
        assert(before::<C>(first, steps, k) == y);
        assert(end::<A>(afirst, all) == t);
    }
}

/// Every trace the concrete model can show that `ok` admits, the abstract
/// model can show: trace inclusion on those traces, from a forward
/// simulation on the steps they are made of.
pub proof fn refines_under<X, R, D, C: Model<External = X, Response = R, Dispatch = D>, A: Model<External = X, Response = R, Dispatch = D>>(
    c: C, a: A, r: spec_fn(Cfg<C>, Cfg<A>) -> bool, ok: spec_fn(Label<X, R, D>) -> bool, ci: C::State, ai: A::State, trace: Seq<Event<X, R, D>>,
)
    requires
        r(initial::<C>(ci), initial::<A>(ai)),
        simulation_under(c, a, r, ok),
        admits(ok, trace),
        valid(c, ci, trace),
    ensures
        valid(a, ai, trace),
{
    let first = initial::<C>(ci);
    let steps = choose|steps: Execution<C>| #![trigger legal(c, first, steps), project::<C>(steps)]
        legal(c, first, steps) && project::<C>(steps) == trace;
    assert forall|i: int| 0 <= i < steps.len() implies #[trigger] ok(steps[i].0) by {
        lemma_labels_admitted::<X, R, D, C>(ok, trace, steps, i);
    }
    lemma_simulate(c, a, r, ok, ci, ai, steps, steps.len() as int);
    assert(steps.take(steps.len() as int) =~= steps);
    let afirst = initial::<A>(ai);
    let asteps = choose|asteps: Execution<A>| #![trigger legal(a, afirst, asteps)]
        legal(a, afirst, asteps)
        && project::<A>(asteps) == project::<C>(steps.take(steps.len() as int))
        && r(before::<C>(first, steps, steps.len() as int), end::<A>(afirst, asteps));
    assert(legal(a, afirst, asteps) && project::<A>(asteps) == trace);
}

/// Every trace the concrete model can show, the abstract model can show:
/// trace inclusion, from a forward simulation.
pub proof fn refines<X, R, D, C: Model<External = X, Response = R, Dispatch = D>, A: Model<External = X, Response = R, Dispatch = D>>(
    c: C, a: A, r: spec_fn(Cfg<C>, Cfg<A>) -> bool, ci: C::State, ai: A::State, trace: Seq<Event<X, R, D>>,
)
    requires
        r(initial::<C>(ci), initial::<A>(ai)),
        simulation(c, a, r),
        valid(c, ci, trace),
    ensures
        valid(a, ai, trace),
{
    let ok = |l: Label<X, R, D>| true;
    assert(admits(ok, trace));
    refines_under(c, a, r, ok, ci, ai, trace);
}

} // verus!
