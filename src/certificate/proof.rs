//! The lemmas behind `certify`'s contract: each replayed step is a step of
//! [`semantics::step`], and a legal execution grows one step at a time into
//! the witness that [`semantics::valid`] asks for.

// Specification and proof only: nothing here survives a plain build.
#![allow(unused_imports)]

use vstd::prelude::*;

use crate::semantics::*;
use crate::{CallId, Model};

verus! {

// ------------------------------------------------- the silent steps, as steps

/// An external op settles: what `Config::silent` computes is an [`effect`] step.
pub(super) proof fn effect_step<M: Model>(m: M, c: Cfg<M>, d: Cfg<M>, call: CallId, j: int)
    requires
        !overdue(m, c),
        c.externals.contains_key(call),
        c.externals[call].res is None,
        0 <= j < m.spec_external(c.externals[call].req, c.state, c.now).len(),
        d == ({
            let o = m.spec_external(c.externals[call].req, c.state, c.now)[j];
            Config {
                state: o.next,
                externals: c.externals.insert(call, ExternalOp { req: c.externals[call].req, res: Some(o.resp) }),
                internals: start_all(c.internals, o.work, c.now),
                sent: c.sent + o.send,
                ..c
            }
        }),
    ensures
        step(m, c, Label::Silent, d),
{
    assert(effect(m, c, Label::Silent, d));
}

/// An internal op runs: what `Config::silent` computes is a [`run`] step.
pub(super) proof fn run_step<M: Model>(m: M, c: Cfg<M>, d: Cfg<M>, i: int, j: int)
    requires
        0 <= i < c.internals.len(),
        ready(c.now, c.internals[i]),
        overdue(m, c) ==> is_first(m, c, i),
        0 <= j < m.spec_internal(req_of(c.internals[i]), c.state, c.now).len(),
        d == ({
            let o = m.spec_internal(req_of(c.internals[i]), c.state, c.now)[j];
            Config {
                state: o.next,
                internals: start_all(c.internals.remove(i), o.work, c.now),
                sent: c.sent + o.send,
                ..c
            }
        }),
    ensures
        step(m, c, Label::Silent, d),
{
    assert(run(m, c, Label::Silent, d));
}

// ------------------------------------------------ executions, step by step

/// A legal execution, extended by a step the system can take from where the
/// execution left it, is legal.
pub(super) proof fn extend<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>, l: Lab<M>, d: Cfg<M>)
    requires
        legal(m, first, steps),
        step(m, before::<M>(first, steps, steps.len() as int), l, d),
    ensures
        legal(m, first, steps.push((l, d))),
        before::<M>(first, steps.push((l, d)), steps.len() as int + 1) == d,
        steps.push((l, d)).drop_last() == steps,
{
    let more = steps.push((l, d));
    assert(more.drop_last() =~= steps);
    assert forall|i: int| 0 <= i < more.len() implies #[trigger] step(m, before::<M>(first, more, i), more[i].0, more[i].1) by {
        if i < steps.len() {
            assert(step(m, before::<M>(first, steps, i), steps[i].0, steps[i].1));
        }
    }
}

/// A silent step shows the client nothing.
pub(super) proof fn silent_step<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>, d: Cfg<M>)
    requires
        legal(m, first, steps),
        step(m, before::<M>(first, steps, steps.len() as int), Label::Silent, d),
    ensures
        legal(m, first, steps.push((Label::Silent, d))),
        before::<M>(first, steps.push((Label::Silent, d)), steps.len() as int + 1) == d,
        project::<M>(steps.push((Label::Silent, d))) == project::<M>(steps),
{
    extend(m, first, steps, Label::Silent, d);
}

/// An observed step shows the client its event: the `k`-th of the trace, once
/// the execution so far shows the first `k`.
pub(super) proof fn observed_step<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>, trace: Seq<Ev<M>>, k: int, d: Cfg<M>)
    requires
        legal(m, first, steps),
        0 <= k < trace.len(),
        project::<M>(steps) == trace.subrange(0, k),
        step(m, before::<M>(first, steps, steps.len() as int), Label::Obs(trace[k]), d),
    ensures
        legal(m, first, steps.push((Label::Obs(trace[k]), d))),
        before::<M>(first, steps.push((Label::Obs(trace[k]), d)), steps.len() as int + 1) == d,
        project::<M>(steps.push((Label::Obs(trace[k]), d))) == trace.subrange(0, k + 1),
{
    extend(m, first, steps, Label::Obs(trace[k]), d);
    assert(project::<M>(steps.push((Label::Obs(trace[k]), d))) =~= trace.subrange(0, k + 1));
}

/// The theorem, assembled: an execution from the initial configuration that
/// is legal and shows exactly the trace is the witness `valid` asks for.
pub(super) proof fn accepted_valid<M: Model>(m: M, init: M::State, steps: Execution<M>, trace: Seq<Ev<M>>)
    requires
        legal(m, initial::<M>(init), steps),
        project::<M>(steps) == trace,
    ensures
        valid(m, init, trace),
{
}

} // verus!
