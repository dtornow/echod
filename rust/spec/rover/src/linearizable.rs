//! What `semantics::valid` means, in terms everyone already knows.
//!
//! For a model that starts no internal work and sends nothing (a register, a
//! key-value store: the model is a sequential object), a trace is `valid`
//! exactly when it is linearizable in Herlihy and Wing's sense:
//!
//! > some order of the calls, each with the response it returned (a call
//! > that never returned may be left out, or given any response), is a
//! > legal sequential run of the object, and respects real time: a call that
//! > returned before another was invoked comes first.
//!
//! [`valid_is_linearizable`] proves it. So for this fragment the step rules in
//! `semantics.rs` need no review of their own: they say linearizability. What
//! remains to review are the rules for internal work, dispatches and time.
//!
//! Herlihy and Wing's histories never reuse an operation; the theorem assumes
//! a trace invokes each call id at most once.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::semantics::{self, Call, Cfg, Ev, Execution, Label};
use crate::{CallId, Event, Model};

verus! {

// --------------------------------------------------------- linearizability

/// A call as a sequential run sees it: its request and its response.
pub struct Op<X, R> {
    pub call: CallId,
    pub req: X,
    pub resp: R,
}

pub type OpOf<M> = Op<<M as Model>::External, <M as Model>::Response>;

/// Event `i` of the trace invokes `c`.
pub open spec fn inv_at<M: Model>(t: Seq<Ev<M>>, i: int, c: CallId) -> bool {
    0 <= i < t.len() && t[i] is Invoke && t[i]->Invoke_call == c
}

/// Event `k` of the trace invokes `call` with `req`.
pub open spec fn invokes<M: Model>(t: Seq<Ev<M>>, k: int, call: CallId, req: M::External) -> bool {
    0 <= k < t.len() && t[k] == Event::<M::External, M::Response, M::Dispatch>::Invoke { call, req }
}

/// The history invokes `op.call`, with `op.req`.
pub open spec fn op_invoked<M: Model>(t: Seq<Ev<M>>, op: OpOf<M>) -> bool {
    exists|k: int| #[trigger] invokes::<M>(t, k, op.call, op.req)
}

/// Event `i` of the trace returns `c`.
pub open spec fn ret_at<M: Model>(t: Seq<Ev<M>>, i: int, c: CallId) -> bool {
    0 <= i < t.len() && t[i] is Return && t[i]->Return_call == c
}

/// A history: invocations and responses only, each response to a call
/// invoked before it, and at most one response per call.
pub open spec fn well_formed<M: Model>(t: Seq<Ev<M>>) -> bool {
    &&& forall|i: int| 0 <= i < t.len() ==> !(#[trigger] t[i] is Receive)
    &&& forall|i: int, c: CallId| #[trigger] ret_at::<M>(t, i, c) ==> exists|k: int| k < i && #[trigger] inv_at::<M>(t, k, c)
    &&& forall|i: int, k: int, c: CallId| #[trigger] ret_at::<M>(t, i, c) && #[trigger] ret_at::<M>(t, k, c) ==> i == k
}

/// Each call id is invoked at most once.
pub open spec fn invoked_once<M: Model>(t: Seq<Ev<M>>) -> bool {
    forall|i: int, k: int, c: CallId| #[trigger] inv_at::<M>(t, i, c) && #[trigger] inv_at::<M>(t, k, c) ==> i == k
}

/// The model takes `s` to `next` on `op.req`, answering `op.resp`.
pub open spec fn seq_step<M: Model>(m: M, s: M::State, op: OpOf<M>, next: M::State) -> bool {
    exists|j: int|
        0 <= j < m.spec_external(op.req, s).len() && #[trigger] m.spec_external(op.req, s)[j].next == next
            && m.spec_external(op.req, s)[j].resp == op.resp
}

/// `ops`, one after the other from `init`, is a run of the model as a
/// sequential object, through `states`.
pub open spec fn seq_run<M: Model>(m: M, init: M::State, ops: Seq<OpOf<M>>, states: Seq<M::State>) -> bool {
    &&& states.len() == ops.len() + 1
    &&& states[0] == init
    &&& forall|p: int| 0 <= p < ops.len() ==> #[trigger] seq_step(m, states[p], ops[p], states[p + 1])
}

/// `ops` linearizes the history `t`.
pub open spec fn linearizes<M: Model>(m: M, init: M::State, t: Seq<Ev<M>>, ops: Seq<OpOf<M>>, states: Seq<M::State>) -> bool {
    // a legal sequential run,
    &&& seq_run(m, init, ops, states)
    // of distinct calls,
    &&& forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] ops[p].call != #[trigger] ops[q].call
    // each one the history invokes, with its request;
    &&& forall|p: int| 0 <= p < ops.len() ==> #[trigger] op_invoked::<M>(t, ops[p])
    // every call that returned is among them, with the response it returned;
    &&& forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return ==> exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res
    // and a call that returned before another was invoked comes first.
    &&& forall|p: int, q: int, i: int, k: int|
        0 <= p < q < ops.len() && #[trigger] ret_at::<M>(t, i, ops[q].call) && #[trigger] inv_at::<M>(t, k, ops[p].call) ==> k < i
}

/// Herlihy and Wing's linearizability, of the model as a sequential object.
pub open spec fn linearizable<M: Model>(m: M, init: M::State, t: Seq<Ev<M>>) -> bool {
    well_formed::<M>(t) && exists|ops: Seq<OpOf<M>>, states: Seq<M::State>| #[trigger] linearizes(m, init, t, ops, states)
}

/// The model starts no internal work and sends nothing.
pub open spec fn plain<M: Model>(m: M) -> bool {
    forall|req: M::External, s: M::State, j: int| 0 <= j < m.spec_external(req, s).len() ==> {
        &&& (#[trigger] m.spec_external(req, s)[j]).work.len() == 0
        &&& m.spec_external(req, s)[j].send.len() == 0
    }
}

// ------------------------------------------------------------------ theorem

/// For a model with no internal work and no dispatches, and a trace that
/// invokes each call once, `valid` is linearizability.
pub proof fn valid_is_linearizable<M: Model>(m: M, init: M::State, t: Seq<Ev<M>>)
    requires
        plain(m),
        invoked_once::<M>(t),
    ensures
        semantics::valid(m, init, t) <==> linearizable(m, init, t),
{
    if semantics::valid(m, init, t) {
        let steps = choose|steps: Execution<M>|
            #![trigger semantics::legal(m, semantics::initial::<M>(init), steps), semantics::project::<M>(steps)]
            semantics::legal(m, semantics::initial::<M>(init), steps) && semantics::project::<M>(steps) == t;
        valid_linearizable(m, init, steps);
    }
    if linearizable(m, init, t) {
        linearizable_valid(m, init, t);
    }
}

// -------------------------------------------- valid ==> linearizable

/// What an execution so far tells about the calls: the order they took
/// effect in (`ops`, through `states`), and for each the number of events
/// shown before it took effect (`eff`).
pub open spec fn tracked<M: Model>(
    m: M,
    init: M::State,
    t: Seq<Ev<M>>,
    cfg: Cfg<M>,
    ops: Seq<OpOf<M>>,
    states: Seq<M::State>,
    eff: Seq<int>,
    inv: Seq<int>,
) -> bool {
    &&& seq_run(m, init, ops, states)
    &&& states[ops.len() as int] == cfg.state
    &&& cfg.work.len() == 0
    &&& cfg.sent.len() == 0
    &&& well_formed::<M>(t)
    &&& forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] ops[p].call != #[trigger] ops[q].call
    &&& eff.len() == ops.len()
    &&& forall|p: int| 0 <= p < ops.len() ==> #[trigger] eff[p] <= t.len()
    &&& forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] eff[p] <= #[trigger] eff[q]
    &&& inv.len() == ops.len()
    &&& forall|p: int| 0 <= p < ops.len() ==> #[trigger] inv[p] < eff[p] && invokes::<M>(t, inv[p], ops[p].call, ops[p].req)
    &&& forall|c: CallId| #[trigger] cfg.calls.contains_key(c) ==> {
        &&& forall|i: int| !ret_at::<M>(t, i, c)
        &&& cfg.calls[c] is InFlight ==> (exists|k: int| #[trigger] invokes::<M>(t, k, c, cfg.calls[c]->InFlight_0))
            && (forall|p: int| 0 <= p < ops.len() ==> ops[p].call != c)
        &&& cfg.calls[c] is Done ==> exists|p: int| 0 <= p < ops.len() && ops[p].call == c && ops[p].resp == cfg.calls[c]->Done_0
    }
    &&& forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return ==> exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res && eff[p] <= i
}

proof fn valid_linearizable<M: Model>(m: M, init: M::State, steps: Execution<M>)
    requires
        plain(m),
        semantics::legal(m, semantics::initial::<M>(init), steps),
        invoked_once::<M>(semantics::project::<M>(steps)),
    ensures
        linearizable(m, init, semantics::project::<M>(steps)),
{
    let t = semantics::project::<M>(steps);
    let (ops, states, eff, inv) = track(m, init, steps);
    // Real time: a call that returned before another was invoked took effect
    // first, since a call takes effect after its invocation and before its
    // return.
    assert forall|p: int, q: int, i: int, k: int|
        0 <= p < q < ops.len() && #[trigger] ret_at::<M>(t, i, ops[q].call) && #[trigger] inv_at::<M>(t, k, ops[p].call) implies k < i by {
        assert(t[i] is Return);
        let q2 = choose|q2: int| 0 <= q2 < ops.len() && ops[q2].call == t[i]->Return_call && ops[q2].resp == t[i]->Return_res && eff[q2] <= i;
        if q2 != q {
            if q2 < q {
                assert(ops[q2].call != ops[q].call);
            } else {
                assert(ops[q].call != ops[q2].call);
            }
        }
        let k0 = inv[p];
        assert(inv[p] < eff[p] && invokes::<M>(t, k0, ops[p].call, ops[p].req));
        assert(inv_at::<M>(t, k0, ops[p].call));
        assert(eff[p] <= eff[q]);
    }
    assert forall|p: int| 0 <= p < ops.len() implies #[trigger] op_invoked::<M>(t, ops[p]) by {
        assert(inv[p] < eff[p] && invokes::<M>(t, inv[p], ops[p].call, ops[p].req));
    }
    assert forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return implies exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res by {
        let p = choose|p: int| 0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res && eff[p] <= i;
    }
    assert(seq_run(m, init, ops, states));
    assert(forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] ops[p].call != #[trigger] ops[q].call);
    assert(forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return ==> exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res);
    assert(forall|p: int, q: int, i: int, k: int|
        0 <= p < q < ops.len() && #[trigger] ret_at::<M>(t, i, ops[q].call) && #[trigger] inv_at::<M>(t, k, ops[p].call) ==> k < i);
    assert(linearizes(m, init, t, ops, states));
}

/// A prefix of a legal execution is legal.
proof fn legal_drop_last<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>)
    requires
        semantics::legal(m, first, steps),
        steps.len() > 0,
    ensures
        semantics::legal(m, first, steps.drop_last()),
        semantics::before::<M>(first, steps, steps.len() - 1) == semantics::before::<M>(first, steps.drop_last(), steps.len() - 1),
{
    let s = steps.drop_last();
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] semantics::step(m, semantics::before::<M>(first, s, i), s[i].0, s[i].1) by {
        assert(semantics::before::<M>(first, s, i) == semantics::before::<M>(first, steps, i));
        assert(semantics::step(m, semantics::before::<M>(first, steps, i), steps[i].0, steps[i].1));
    }
}

/// The projection of all but the last step: the same, or one event fewer.
proof fn project_drop_last<M: Model>(steps: Execution<M>)
    requires
        steps.len() > 0,
    ensures
        ({
            let t = semantics::project::<M>(steps);
            let s = semantics::project::<M>(steps.drop_last());
            match steps.last().0 {
                Label::Obs(e) => t == s.push(e),
                Label::Silent => t == s,
            }
        }),
{
}

/// Calls invoked once in a history are invoked once in its prefix.
proof fn invoked_once_prefix<M: Model>(t: Seq<Ev<M>>, s: Seq<Ev<M>>)
    requires
        invoked_once::<M>(t),
        s.len() <= t.len(),
        s == t.subrange(0, s.len() as int),
    ensures
        invoked_once::<M>(s),
{
    assert forall|i: int, k: int, c: CallId| #[trigger] inv_at::<M>(s, i, c) && #[trigger] inv_at::<M>(s, k, c) implies i == k by {
        assert(s[i] == t[i]);
        assert(s[k] == t[k]);
        assert(inv_at::<M>(t, i, c) && inv_at::<M>(t, k, c));
    }
}

/// What an execution tells about the calls, step by step.
proof fn track<M: Model>(m: M, init: M::State, steps: Execution<M>) -> (r: (Seq<OpOf<M>>, Seq<M::State>, Seq<int>, Seq<int>))
    requires
        plain(m),
        semantics::legal(m, semantics::initial::<M>(init), steps),
        invoked_once::<M>(semantics::project::<M>(steps)),
    ensures
        tracked(
            m,
            init,
            semantics::project::<M>(steps),
            semantics::before::<M>(semantics::initial::<M>(init), steps, steps.len() as int),
            r.0,
            r.1,
            r.2,
            r.3,
        ),
    decreases steps.len(),
{
    let first = semantics::initial::<M>(init);
    if steps.len() == 0 {
        let ops = Seq::<OpOf<M>>::empty();
        let states = seq![init];
        let eff = Seq::<int>::empty();
        let inv = Seq::<int>::empty();
        assert(semantics::project::<M>(steps) =~= Seq::<Ev<M>>::empty());
        assert(tracked(m, init, semantics::project::<M>(steps), first, ops, states, eff, inv));
        return (ops, states, eff, inv);
    }
    let s = steps.drop_last();
    let t = semantics::project::<M>(steps);
    let ts = semantics::project::<M>(s);
    legal_drop_last(m, first, steps);
    project_drop_last::<M>(steps);
    assert(ts == t.subrange(0, ts.len() as int)) by {
        match steps.last().0 {
            Label::Obs(e) => {
                assert(t == ts.push(e));
                assert(ts =~= ts.push(e).subrange(0, ts.len() as int));
            }
            Label::Silent => {
                assert(ts =~= ts.subrange(0, ts.len() as int));
            }
        }
    }
    invoked_once_prefix::<M>(t, ts);
    let (ops, states, eff, inv) = track(m, init, s);
    let n = steps.len() - 1;
    let c = semantics::before::<M>(first, s, n);
    assert(c == semantics::before::<M>(first, steps, n));
    let (l, d) = steps[n];
    assert(semantics::step(m, c, l, d));
    assert(semantics::before::<M>(first, steps, steps.len() as int) == d);
    assert(steps.last() == (l, d));
    if semantics::invoke(m, c, l, d) {
        let e = l->Obs_0;
        let call = e->Invoke_call;
        assert(t == ts.push(e));
        assert(inv_at::<M>(t, ts.len() as int, call));
        // `call` is new: invoked nowhere before, so not among the calls that took effect.
        assert forall|p: int| 0 <= p < ops.len() implies ops[p].call != call by {
            let k0 = inv[p];
            assert(inv[p] < eff[p] && invokes::<M>(ts, k0, ops[p].call, ops[p].req));
            assert(t[k0] == ts[k0]);
            if ops[p].call == call {
                assert(inv_at::<M>(t, k0, call));
            }
        }
        assert forall|i: int| !ret_at::<M>(t, i, call) by {
            if ret_at::<M>(t, i, call) {
                assert(i < ts.len());
                assert(ret_at::<M>(ts, i, call)) by { assert(ts[i] == t[i]); }
                let k = choose|k: int| k < i && #[trigger] inv_at::<M>(ts, k, call);
                assert(inv_at::<M>(t, k, call)) by { assert(ts[k] == t[k]); }
            }
        }
        lemma_tracked_extend(m, init, ts, t, c, d, ops, states, eff, inv);
        return (ops, states, eff, inv);
    } else if semantics::ret(m, c, l, d) {
        let e = l->Obs_0;
        assert(t == ts.push(e));
        lemma_tracked_return(m, init, ts, t, c, d, ops, states, eff, inv);
        return (ops, states, eff, inv);
    } else if semantics::receive(m, c, l, d) {
        assert(false);
        return (ops, states, eff, inv);
    } else if semantics::effect(m, c, l, d) {
        assert(t == ts);
        let (call, j) = choose|call: CallId, j: int|
            #![trigger c.calls[call], m.spec_external(c.calls[call]->InFlight_0, c.state)[j]]
            c.calls.contains_key(call) && c.calls[call] is InFlight && {
                let outs = m.spec_external(c.calls[call]->InFlight_0, c.state);
                0 <= j < outs.len() && d == semantics::Config {
                    state: outs[j].next,
                    calls: c.calls.insert(call, Call::Done(outs[j].resp)),
                    work: semantics::start_all(c.work, outs[j].work, m.spec_now(outs[j].next)),
                    sent: c.sent + outs[j].send,
                    ..c
                }
            };
        let req = c.calls[call]->InFlight_0;
        let o = m.spec_external(req, c.state)[j];
        let op = Op { call, req, resp: o.resp };
        let ops2 = ops.push(op);
        let states2 = states.push(o.next);
        let eff2 = eff.push(ts.len() as int);
        assert(c.calls.contains_key(call));
        let k = choose|k: int| #[trigger] invokes::<M>(ts, k, call, c.calls[call]->InFlight_0);
        lemma_tracked_effect(m, init, ts, c, d, ops, states, eff, inv, call, j, k);
        return (ops2, states2, eff2, inv.push(k));
    } else {
        assert(semantics::run(m, c, l, d));
        assert(false);
        return (ops, states, eff, inv);
    }
}

/// An invocation keeps what is tracked.
proof fn lemma_tracked_extend<M: Model>(
    m: M,
    init: M::State,
    ts: Seq<Ev<M>>,
    t: Seq<Ev<M>>,
    c: Cfg<M>,
    d: Cfg<M>,
    ops: Seq<OpOf<M>>,
    states: Seq<M::State>,
    eff: Seq<int>,
    inv: Seq<int>,
)
    requires
        tracked(m, init, ts, c, ops, states, eff, inv),
        t.len() == ts.len() + 1,
        ts == t.subrange(0, ts.len() as int),
        t.last() is Invoke,
        invoked_once::<M>(t),
        d == (semantics::Config { calls: c.calls.insert(t.last()->Invoke_call, Call::InFlight(t.last()->Invoke_req)), ..c }),
        forall|p: int| 0 <= p < ops.len() ==> ops[p].call != t.last()->Invoke_call,
        forall|i: int| !ret_at::<M>(t, i, t.last()->Invoke_call),
    ensures
        tracked(m, init, t, d, ops, states, eff, inv),
{
    let call = t.last()->Invoke_call;
    assert forall|i: int| 0 <= i < ts.len() implies #[trigger] t[i] == ts[i] by {}
    assert(t[ts.len() as int] == t.last());
    // well-formed
    assert forall|i: int, x: CallId| #[trigger] ret_at::<M>(t, i, x) implies exists|k: int| k < i && #[trigger] inv_at::<M>(t, k, x) by {
        assert(i < ts.len());
        assert(ret_at::<M>(ts, i, x));
        let k = choose|k: int| k < i && #[trigger] inv_at::<M>(ts, k, x);
        assert(inv_at::<M>(t, k, x));
    }
    assert forall|i: int, k: int, x: CallId| #[trigger] ret_at::<M>(t, i, x) && #[trigger] ret_at::<M>(t, k, x) implies i == k by {
        assert(ret_at::<M>(ts, i, x) && ret_at::<M>(ts, k, x));
    }
    assert forall|i: int| 0 <= i < t.len() implies !(#[trigger] t[i] is Receive) by {
        if i < ts.len() {
            assert(!(ts[i] is Receive));
        }
    }
    // invocations, before what took effect
    assert forall|p: int| 0 <= p < ops.len() implies #[trigger] inv[p] < eff[p] && invokes::<M>(t, inv[p], ops[p].call, ops[p].req) by {
        assert(inv[p] < eff[p] && invokes::<M>(ts, inv[p], ops[p].call, ops[p].req));
        assert(t[inv[p]] == ts[inv[p]]);
    }
    // the calls
    assert forall|x: CallId| #[trigger] d.calls.contains_key(x) implies {
        &&& forall|i: int| !ret_at::<M>(t, i, x)
        &&& d.calls[x] is InFlight ==> (exists|k: int| #[trigger] invokes::<M>(t, k, x, d.calls[x]->InFlight_0))
            && (forall|p: int| 0 <= p < ops.len() ==> ops[p].call != x)
        &&& d.calls[x] is Done ==> exists|p: int| 0 <= p < ops.len() && ops[p].call == x && ops[p].resp == d.calls[x]->Done_0
    } by {
        if x == call {
            assert(t[ts.len() as int] == Event::Invoke { call: x, req: d.calls[x]->InFlight_0 });
            assert(invokes::<M>(t, ts.len() as int, x, d.calls[x]->InFlight_0));
        } else {
            assert(c.calls.contains_key(x));
            assert forall|i: int| !ret_at::<M>(t, i, x) by {
                if ret_at::<M>(t, i, x) {
                    assert(i < ts.len());
                    assert(ret_at::<M>(ts, i, x));
                }
            }
            if d.calls[x] is InFlight {
                let k = choose|k: int| #[trigger] invokes::<M>(ts, k, x, c.calls[x]->InFlight_0);
                assert(t[k] == ts[k]);
            assert(d.calls[x] == c.calls[x]);
            assert(invokes::<M>(t, k, x, d.calls[x]->InFlight_0));
            }
        }
    }
    assert forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return implies exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res && eff[p] <= i by {
        assert(i < ts.len());
        assert(ts[i] is Return);
    }
    assert forall|p: int| 0 <= p < ops.len() implies #[trigger] eff[p] <= t.len() by {}
    assert(seq_run(m, init, ops, states));
    assert(states[ops.len() as int] == d.state);
    assert(d.work.len() == 0);
    assert(d.sent.len() == 0);
    assert(well_formed::<M>(t));
    assert(forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] ops[p].call != #[trigger] ops[q].call);
    assert(eff.len() == ops.len());
    assert(forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] eff[p] <= #[trigger] eff[q]);
    assert(inv.len() == ops.len());
    assert(forall|x: CallId| #[trigger] d.calls.contains_key(x) ==> {
        &&& forall|i: int| !ret_at::<M>(t, i, x)
        &&& d.calls[x] is InFlight ==> (exists|k: int| #[trigger] invokes::<M>(t, k, x, d.calls[x]->InFlight_0))
            && (forall|p: int| 0 <= p < ops.len() ==> ops[p].call != x)
        &&& d.calls[x] is Done ==> exists|p: int| 0 <= p < ops.len() && ops[p].call == x && ops[p].resp == d.calls[x]->Done_0
    });
    assert(forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return ==> exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res && eff[p] <= i);
}

/// A return keeps what is tracked.
proof fn lemma_tracked_return<M: Model>(
    m: M,
    init: M::State,
    ts: Seq<Ev<M>>,
    t: Seq<Ev<M>>,
    c: Cfg<M>,
    d: Cfg<M>,
    ops: Seq<OpOf<M>>,
    states: Seq<M::State>,
    eff: Seq<int>,
    inv: Seq<int>,
)
    requires
        tracked(m, init, ts, c, ops, states, eff, inv),
        t.len() == ts.len() + 1,
        ts == t.subrange(0, ts.len() as int),
        semantics::ret(m, c, Label::Obs(t.last()), d),
    ensures
        tracked(m, init, t, d, ops, states, eff, inv),
{
    let e = t.last();
    let call = e->Return_call;
    let res = e->Return_res;
    let n = ts.len() as int;
    assert(t[n] == e);
    assert forall|i: int| 0 <= i < ts.len() implies #[trigger] t[i] == ts[i] by {}
    assert(c.calls.contains_key(call) && c.calls[call] is Done && c.calls[call]->Done_0 == res);
    assert(d.calls == c.calls.remove(call));
    assert(c.calls[call] is Done ==> exists|p: int| 0 <= p < ops.len() && ops[p].call == call && ops[p].resp == c.calls[call]->Done_0);
    let p0 = choose|p: int| 0 <= p < ops.len() && ops[p].call == call && ops[p].resp == c.calls[call]->Done_0;
    assert(ops[p0].call == call);
    // well-formed
    assert forall|i: int, x: CallId| #[trigger] ret_at::<M>(t, i, x) implies exists|k: int| k < i && #[trigger] inv_at::<M>(t, k, x) by {
        if i < n {
            assert(ret_at::<M>(ts, i, x));
            let k = choose|k: int| k < i && #[trigger] inv_at::<M>(ts, k, x);
            assert(inv_at::<M>(t, k, x));
        } else {
            let k0 = inv[p0];
            assert(inv[p0] < eff[p0] && invokes::<M>(ts, k0, ops[p0].call, ops[p0].req));
            assert(t[k0] == ts[k0]);
            assert(inv_at::<M>(t, k0, x));
        }
    }
    assert forall|i: int, k: int, x: CallId| #[trigger] ret_at::<M>(t, i, x) && #[trigger] ret_at::<M>(t, k, x) implies i == k by {
        if i < n && k < n {
            assert(ret_at::<M>(ts, i, x) && ret_at::<M>(ts, k, x));
        } else if i < n {
            assert(ret_at::<M>(ts, i, call));
        } else if k < n {
            assert(ret_at::<M>(ts, k, call));
        }
    }
    assert forall|i: int| 0 <= i < t.len() implies !(#[trigger] t[i] is Receive) by {
        if i < n {
            assert(!(ts[i] is Receive));
        }
    }
    assert forall|p: int| 0 <= p < ops.len() implies #[trigger] inv[p] < eff[p] && invokes::<M>(t, inv[p], ops[p].call, ops[p].req) by {
        assert(inv[p] < eff[p] && invokes::<M>(ts, inv[p], ops[p].call, ops[p].req));
        assert(t[inv[p]] == ts[inv[p]]);
    }
    assert forall|x: CallId| #[trigger] d.calls.contains_key(x) implies {
        &&& forall|i: int| !ret_at::<M>(t, i, x)
        &&& d.calls[x] is InFlight ==> (exists|k: int| #[trigger] invokes::<M>(t, k, x, d.calls[x]->InFlight_0))
            && (forall|p: int| 0 <= p < ops.len() ==> ops[p].call != x)
        &&& d.calls[x] is Done ==> exists|p: int| 0 <= p < ops.len() && ops[p].call == x && ops[p].resp == d.calls[x]->Done_0
    } by {
        assert(x != call);
        assert(c.calls.contains_key(x));
        assert forall|i: int| !ret_at::<M>(t, i, x) by {
            if ret_at::<M>(t, i, x) && i < n {
                assert(ret_at::<M>(ts, i, x));
            }
        }
        if d.calls[x] is InFlight {
            let k = choose|k: int| #[trigger] invokes::<M>(ts, k, x, c.calls[x]->InFlight_0);
            assert(t[k] == ts[k]);
            assert(d.calls[x] == c.calls[x]);
            assert(invokes::<M>(t, k, x, d.calls[x]->InFlight_0));
        }
    }
    assert forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return implies exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res && eff[p] <= i by {
        if i < n {
            assert(ts[i] is Return);
        } else {
            assert(eff[p0] <= ts.len());
        }
    }
    assert forall|p: int| 0 <= p < ops.len() implies #[trigger] eff[p] <= t.len() by {}
    assert(seq_run(m, init, ops, states));
    assert(states[ops.len() as int] == d.state);
    assert(d.work.len() == 0);
    assert(d.sent.len() == 0);
    assert(well_formed::<M>(t));
    assert(forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] ops[p].call != #[trigger] ops[q].call);
    assert(eff.len() == ops.len());
    assert(forall|p: int, q: int| 0 <= p < q < ops.len() ==> #[trigger] eff[p] <= #[trigger] eff[q]);
    assert(inv.len() == ops.len());
    assert(forall|x: CallId| #[trigger] d.calls.contains_key(x) ==> {
        &&& forall|i: int| !ret_at::<M>(t, i, x)
        &&& d.calls[x] is InFlight ==> (exists|k: int| #[trigger] invokes::<M>(t, k, x, d.calls[x]->InFlight_0))
            && (forall|p: int| 0 <= p < ops.len() ==> ops[p].call != x)
        &&& d.calls[x] is Done ==> exists|p: int| 0 <= p < ops.len() && ops[p].call == x && ops[p].resp == d.calls[x]->Done_0
    });
    assert(forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return ==> exists|p: int|
        0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res && eff[p] <= i);
}

/// A call taking effect extends what is tracked by it.
proof fn lemma_tracked_effect<M: Model>(
    m: M,
    init: M::State,
    t: Seq<Ev<M>>,
    c: Cfg<M>,
    d: Cfg<M>,
    ops: Seq<OpOf<M>>,
    states: Seq<M::State>,
    eff: Seq<int>,
    inv: Seq<int>,
    call: CallId,
    j: int,
    k: int,
)
    requires
        plain(m),
        tracked(m, init, t, c, ops, states, eff, inv),
        invokes::<M>(t, k, call, c.calls[call]->InFlight_0),
        c.calls.contains_key(call),
        c.calls[call] is InFlight,
        0 <= j < m.spec_external(c.calls[call]->InFlight_0, c.state).len(),
        d == ({
            let o = m.spec_external(c.calls[call]->InFlight_0, c.state)[j];
            semantics::Config {
                state: o.next,
                calls: c.calls.insert(call, Call::Done(o.resp)),
                work: semantics::start_all(c.work, o.work, m.spec_now(o.next)),
                sent: c.sent + o.send,
            }
        }),
    ensures
        ({
            let req = c.calls[call]->InFlight_0;
            let o = m.spec_external(req, c.state)[j];
            tracked(m, init, t, d, ops.push(Op { call, req, resp: o.resp }), states.push(o.next), eff.push(t.len() as int), inv.push(k))
        }),
{
    let req = c.calls[call]->InFlight_0;
    let o = m.spec_external(req, c.state)[j];
    let op = Op { call, req, resp: o.resp };
    let ops2 = ops.push(op);
    let states2 = states.push(o.next);
    let eff2 = eff.push(t.len() as int);
    let n = ops.len() as int;
    assert(o.work.len() == 0 && o.send.len() == 0);
    assert(d.work =~= c.work);
    assert(d.sent =~= c.sent);
    // the sequential run, one step longer
    assert(seq_run(m, init, ops, states));
    assert(states.len() == n + 1);
    assert(states2[n] == c.state);
    assert(states2[n + 1] == o.next);
    assert(ops2[n] == op);
    assert(m.spec_external(op.req, states2[n])[j].next == states2[n + 1]);
    assert(seq_step(m, states2[n], ops2[n], states2[n + 1]));
    assert forall|p: int| 0 <= p < ops2.len() implies #[trigger] seq_step(m, states2[p], ops2[p], states2[p + 1]) by {
        if p < n {
            assert(seq_step(m, states[p], ops[p], states[p + 1]));
        }
    }
    assert(seq_run(m, init, ops2, states2));
    // distinct: `call` was in flight, so not among those that took effect
    assert forall|p: int, q: int| 0 <= p < q < ops2.len() implies #[trigger] ops2[p].call != #[trigger] ops2[q].call by {
        if q == n {
            assert(ops[p].call != call);
        } else {
            assert(ops[p].call != ops[q].call);
        }
    }
    assert forall|p: int, q: int| 0 <= p < q < ops2.len() implies #[trigger] eff2[p] <= #[trigger] eff2[q] by {
        if q < n {
            assert(eff[p] <= eff[q]);
        } else {
            assert(eff[p] <= t.len());
        }
    }
    assert forall|p: int| 0 <= p < ops2.len() implies #[trigger] eff2[p] <= t.len() by {
        if p < n {
            assert(eff[p] <= t.len());
        }
    }
    let inv2 = inv.push(k);
    assert forall|p: int| 0 <= p < ops2.len() implies #[trigger] inv2[p] < eff2[p] && invokes::<M>(t, inv2[p], ops2[p].call, ops2[p].req) by {
        if p < n {
            assert(inv2[p] == inv[p] && eff2[p] == eff[p] && ops2[p] == ops[p]);
            assert(inv[p] < eff[p] && invokes::<M>(t, inv[p], ops[p].call, ops[p].req));
        } else {
            assert(inv2[p] == k && eff2[p] == t.len() && ops2[p] == op);
        }
    }
    assert forall|x: CallId| #[trigger] d.calls.contains_key(x) implies {
        &&& forall|i: int| !ret_at::<M>(t, i, x)
        &&& d.calls[x] is InFlight ==> (exists|k: int| #[trigger] invokes::<M>(t, k, x, d.calls[x]->InFlight_0))
            && (forall|p: int| 0 <= p < ops2.len() ==> ops2[p].call != x)
        &&& d.calls[x] is Done ==> exists|p: int| 0 <= p < ops2.len() && ops2[p].call == x && ops2[p].resp == d.calls[x]->Done_0
    } by {
        assert(c.calls.contains_key(x));
        if x == call {
            assert(ops2[n].call == x && ops2[n].resp == d.calls[x]->Done_0);
        } else {
            assert(d.calls[x] == c.calls[x]);
            if c.calls[x] is Done {
                let p = choose|p: int| 0 <= p < ops.len() && ops[p].call == x && ops[p].resp == c.calls[x]->Done_0;
                assert(ops2[p] == ops[p]);
            }
        }
    }
    assert forall|i: int| 0 <= i < t.len() && #[trigger] t[i] is Return implies exists|p: int|
        0 <= p < ops2.len() && ops2[p].call == t[i]->Return_call && ops2[p].resp == t[i]->Return_res && eff2[p] <= i by {
        let p = choose|p: int| 0 <= p < ops.len() && ops[p].call == t[i]->Return_call && ops[p].resp == t[i]->Return_res && eff[p] <= i;
        assert(ops2[p] == ops[p] && eff2[p] == eff[p]);
    }
}

// -------------------------------------------- linearizable ==> valid

/// Some event before `i` invokes `c`.
pub open spec fn invoked_before<M: Model>(t: Seq<Ev<M>>, i: int, c: CallId) -> bool {
    exists|k: int| k < i && #[trigger] inv_at::<M>(t, k, c)
}

/// Some event before `i` returns `c`.
pub open spec fn returned_before<M: Model>(t: Seq<Ev<M>>, i: int, c: CallId) -> bool {
    exists|k: int| k < i && #[trigger] ret_at::<M>(t, k, c)
}

/// The configuration after the first `i` events, with the first `p` calls of
/// the linearization taken effect.
pub open spec fn built<M: Model>(m: M, t: Seq<Ev<M>>, ops: Seq<OpOf<M>>, states: Seq<M::State>, i: int, p: int, cfg: Cfg<M>) -> bool {
    &&& 0 <= p <= ops.len()
    &&& states.len() == ops.len() + 1
    &&& cfg.state == states[p]
    &&& cfg.work.len() == 0
    &&& cfg.sent.len() == 0
    &&& forall|q: int| 0 <= q < p ==> #[trigger] invoked_before::<M>(t, i, ops[q].call)
    &&& forall|q: int| p <= q < ops.len() ==> !#[trigger] returned_before::<M>(t, i, ops[q].call)
    &&& forall|c: CallId| #[trigger] cfg.calls.contains_key(c) <==> (invoked_before::<M>(t, i, c) && !returned_before::<M>(t, i, c))
    &&& forall|q: int| 0 <= q < p && #[trigger] cfg.calls.contains_key(ops[q].call) ==> cfg.calls[ops[q].call] == Call::<M::External, M::Response>::Done(ops[q].resp)
    &&& forall|c: CallId, k: int|
        #[trigger] cfg.calls.contains_key(c) && #[trigger] inv_at::<M>(t, k, c) && (forall|q: int| 0 <= q < p ==> ops[q].call != c)
            ==> cfg.calls[c] == Call::<M::External, M::Response>::InFlight(t[k]->Invoke_req)
}

proof fn linearizable_valid<M: Model>(m: M, init: M::State, t: Seq<Ev<M>>)
    requires
        plain(m),
        invoked_once::<M>(t),
        linearizable(m, init, t),
    ensures
        semantics::valid(m, init, t),
{
    let (ops, states) = choose|ops: Seq<OpOf<M>>, states: Seq<M::State>| #[trigger] linearizes(m, init, t, ops, states);
    let (steps, p) = build(m, init, t, ops, states, t.len() as int);
    assert(t.subrange(0, t.len() as int) =~= t);
    assert(semantics::legal(m, semantics::initial::<M>(init), steps) && semantics::project::<M>(steps) == t);
}

/// Nothing is overdue when no work is pending.
proof fn no_overdue<M: Model>(m: M, c: Cfg<M>)
    requires
        c.work.len() == 0,
    ensures
        !semantics::overdue(m, c),
{
    if semantics::overdue(m, c) {
        let i = choose|i: int| #[trigger] semantics::is_overdue(m, c, i);
    }
}

/// A legal execution extended by a step from where it left off.
proof fn extend<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>, l: semantics::Lab<M>, d: Cfg<M>)
    requires
        semantics::legal(m, first, steps),
        semantics::step(m, semantics::before::<M>(first, steps, steps.len() as int), l, d),
    ensures
        semantics::legal(m, first, steps.push((l, d))),
        semantics::before::<M>(first, steps.push((l, d)), steps.len() as int + 1) == d,
        semantics::project::<M>(steps.push((l, d))) == match l {
            Label::Obs(e) => semantics::project::<M>(steps).push(e),
            Label::Silent => semantics::project::<M>(steps),
        },
{
    let more = steps.push((l, d));
    assert(more.drop_last() =~= steps);
    assert forall|i: int| 0 <= i < more.len() implies #[trigger] semantics::step(m, semantics::before::<M>(first, more, i), more[i].0, more[i].1) by {
        if i < steps.len() {
            assert(semantics::step(m, semantics::before::<M>(first, steps, i), steps[i].0, steps[i].1));
        }
    }
}

/// The execution showing the first `i` events, and the linearization's
/// progress `p`.
proof fn build<M: Model>(m: M, init: M::State, t: Seq<Ev<M>>, ops: Seq<OpOf<M>>, states: Seq<M::State>, i: int) -> (r: (Execution<M>, int))
    requires
        plain(m),
        invoked_once::<M>(t),
        well_formed::<M>(t),
        linearizes(m, init, t, ops, states),
        0 <= i <= t.len(),
    ensures
        semantics::legal(m, semantics::initial::<M>(init), r.0),
        semantics::project::<M>(r.0) == t.subrange(0, i),
        built(m, t, ops, states, i, r.1, semantics::before::<M>(semantics::initial::<M>(init), r.0, r.0.len() as int)),
    decreases i,
{
    let first = semantics::initial::<M>(init);
    if i == 0 {
        let steps = Execution::<M>::empty();
        assert(semantics::project::<M>(steps) =~= t.subrange(0, 0));
        assert forall|c: CallId| !#[trigger] invoked_before::<M>(t, 0, c) by {}
        assert forall|c: CallId| !#[trigger] returned_before::<M>(t, 0, c) by {}
        assert forall|q: int| 0 <= q < ops.len() implies !#[trigger] returned_before::<M>(t, 0, ops[q].call) by {}
        return (steps, 0);
    }
    let (steps, p) = build(m, init, t, ops, states, i - 1);
    let cfg = semantics::before::<M>(first, steps, steps.len() as int);
    let e = t[i - 1];
    no_overdue(m, cfg);
    assert(t.subrange(0, i) =~= t.subrange(0, i - 1).push(e));
    match e {
        Event::Invoke { call, req } => {
            let d = semantics::Config { calls: cfg.calls.insert(call, Call::InFlight(req)), ..cfg };
            assert(inv_at::<M>(t, i - 1, call));
            // `call` is new: invoked once, here.
            assert(!cfg.calls.contains_key(call)) by {
                if cfg.calls.contains_key(call) {
                    let k = choose|k: int| k < i - 1 && #[trigger] inv_at::<M>(t, k, call);
                }
            }
            assert(semantics::invoke(m, cfg, Label::Obs(e), d));
            extend(m, first, steps, Label::Obs(e), d);
            let steps2 = steps.push((Label::Obs(e), d));
            lemma_built_invoke(m, t, ops, states, i, p, cfg, d);
            (steps2, p)
        },
        Event::Return { call, res } => {
            assert(ret_at::<M>(t, i - 1, call));
            assert(t[i - 1] is Return);
            let pos = choose|pos: int| 0 <= pos < ops.len() && ops[pos].call == call && ops[pos].resp == res;
            let (steps1, p1) = if pos >= p {
                // The calls up to `call` in the linearization take effect now:
                // each was invoked already (real time).
                assert forall|q: int| p <= q < pos + 1 implies #[trigger] invoked_before::<M>(t, i - 1, ops[q].call) by {
                    assert(op_invoked::<M>(t, ops[q]));
                    let k = choose|k: int| #[trigger] invokes::<M>(t, k, ops[q].call, ops[q].req);
                    assert(inv_at::<M>(t, k, ops[q].call));
                    if q < pos {
                        assert(ret_at::<M>(t, i - 1, ops[pos].call));
                        assert(k < i - 1);
                    } else {
                        let k2 = choose|k2: int| k2 < i - 1 && #[trigger] inv_at::<M>(t, k2, call);
                    }
                }
                apply(m, init, t, ops, states, i - 1, steps, p, pos + 1)
            } else {
                (steps, p)
            };
            let cfg1 = semantics::before::<M>(first, steps1, steps1.len() as int);
            no_overdue(m, cfg1);
            // `call` is in flight or answered: invoked, and not returned before.
            let k2 = choose|k2: int| k2 < i - 1 && #[trigger] inv_at::<M>(t, k2, call);
            assert(invoked_before::<M>(t, i - 1, call));
            assert(!returned_before::<M>(t, i - 1, call)) by {
                if returned_before::<M>(t, i - 1, call) {
                    let r = choose|r: int| r < i - 1 && #[trigger] ret_at::<M>(t, r, call);
                }
            }
            assert(cfg1.calls.contains_key(ops[pos].call));
            assert(cfg1.calls[call] == Call::<M::External, M::Response>::Done(res));
            let d = semantics::Config { calls: cfg1.calls.remove(call), ..cfg1 };
            assert(semantics::ret(m, cfg1, Label::Obs(e), d));
            extend(m, first, steps1, Label::Obs(e), d);
            let steps2 = steps1.push((Label::Obs(e), d));
            lemma_built_return(m, t, ops, states, i, p1, pos, cfg1, d);
            (steps2, p1)
        },
        Event::Receive { .. } => {
            assert(!(t[i - 1] is Receive));
            (steps, p)
        },
    }
}

/// The linearization's calls `p..target` take effect, in order.
proof fn apply<M: Model>(
    m: M,
    init: M::State,
    t: Seq<Ev<M>>,
    ops: Seq<OpOf<M>>,
    states: Seq<M::State>,
    i: int,
    steps: Execution<M>,
    p: int,
    target: int,
) -> (r: (Execution<M>, int))
    requires
        plain(m),
        invoked_once::<M>(t),
        well_formed::<M>(t),
        linearizes(m, init, t, ops, states),
        0 <= i <= t.len(),
        semantics::legal(m, semantics::initial::<M>(init), steps),
        semantics::project::<M>(steps) == t.subrange(0, i),
        built(m, t, ops, states, i, p, semantics::before::<M>(semantics::initial::<M>(init), steps, steps.len() as int)),
        p <= target <= ops.len(),
        forall|q: int| p <= q < target ==> #[trigger] invoked_before::<M>(t, i, ops[q].call),
    ensures
        semantics::legal(m, semantics::initial::<M>(init), r.0),
        semantics::project::<M>(r.0) == t.subrange(0, i),
        r.1 == target,
        built(m, t, ops, states, i, target, semantics::before::<M>(semantics::initial::<M>(init), r.0, r.0.len() as int)),
    decreases target - p,
{
    let first = semantics::initial::<M>(init);
    if p == target {
        return (steps, p);
    }
    let cfg = semantics::before::<M>(first, steps, steps.len() as int);
    no_overdue(m, cfg);
    let c = ops[p].call;
    assert(invoked_before::<M>(t, i, c));
    assert(!returned_before::<M>(t, i, c));
    assert(cfg.calls.contains_key(c));
    // in flight, with its request
    assert(op_invoked::<M>(t, ops[p]));
    let k = choose|k: int| #[trigger] invokes::<M>(t, k, ops[p].call, ops[p].req);
    assert(inv_at::<M>(t, k, c));
    assert forall|q: int| 0 <= q < p implies ops[q].call != c by {
        assert(ops[q].call != ops[p].call);
    }
    assert(cfg.calls[c] == Call::<M::External, M::Response>::InFlight(ops[p].req));
    // with the outcome the sequential run takes
    assert(seq_step(m, states[p], ops[p], states[p + 1]));
    let j = choose|j: int|
        0 <= j < m.spec_external(ops[p].req, states[p]).len() && #[trigger] m.spec_external(ops[p].req, states[p])[j].next == states[p + 1]
            && m.spec_external(ops[p].req, states[p])[j].resp == ops[p].resp;
    let o = m.spec_external(ops[p].req, cfg.state)[j];
    assert(o.work.len() == 0 && o.send.len() == 0);
    let d = semantics::Config {
        state: o.next,
        calls: cfg.calls.insert(c, Call::Done(o.resp)),
        work: semantics::start_all(cfg.work, o.work, m.spec_now(o.next)),
        sent: cfg.sent + o.send,
    };
    assert(cfg.calls[c]->InFlight_0 == ops[p].req);
    assert(m.spec_external(cfg.calls[c]->InFlight_0, cfg.state)[j] == o);
    assert(semantics::effect(m, cfg, Label::Silent, d));
    extend(m, first, steps, Label::Silent, d);
    let steps2 = steps.push((Label::Silent, d));
    assert(d.work =~= cfg.work);
    assert(d.sent =~= cfg.sent);
    lemma_built_effect(m, t, ops, states, i, p, cfg, d);
    apply(m, init, t, ops, states, i, steps2, p + 1, target)
}

/// After an invocation.
proof fn lemma_built_invoke<M: Model>(m: M, t: Seq<Ev<M>>, ops: Seq<OpOf<M>>, states: Seq<M::State>, i: int, p: int, cfg: Cfg<M>, d: Cfg<M>)
    requires
        invoked_once::<M>(t),
        well_formed::<M>(t),
        0 < i <= t.len(),
        t[i - 1] is Invoke,
        built(m, t, ops, states, i - 1, p, cfg),
        !cfg.calls.contains_key(t[i - 1]->Invoke_call),
        d == (semantics::Config { calls: cfg.calls.insert(t[i - 1]->Invoke_call, Call::InFlight(t[i - 1]->Invoke_req)), ..cfg }),
    ensures
        built(m, t, ops, states, i, p, d),
{
    let call = t[i - 1]->Invoke_call;
    assert(inv_at::<M>(t, i - 1, call));
    assert forall|x: CallId| #[trigger] invoked_before::<M>(t, i, x) <==> (invoked_before::<M>(t, i - 1, x) || x == call) by {
        if invoked_before::<M>(t, i, x) {
            let k = choose|k: int| k < i && #[trigger] inv_at::<M>(t, k, x);
            if k < i - 1 {
                assert(invoked_before::<M>(t, i - 1, x));
            }
        }
        if invoked_before::<M>(t, i - 1, x) {
            let k = choose|k: int| k < i - 1 && #[trigger] inv_at::<M>(t, k, x);
            assert(k < i);
        }
    }
    assert forall|x: CallId| #[trigger] returned_before::<M>(t, i, x) <==> returned_before::<M>(t, i - 1, x) by {
        if returned_before::<M>(t, i, x) {
            let k = choose|k: int| k < i && #[trigger] ret_at::<M>(t, k, x);
            assert(k != i - 1);
        }
        if returned_before::<M>(t, i - 1, x) {
            let k = choose|k: int| k < i - 1 && #[trigger] ret_at::<M>(t, k, x);
            assert(k < i);
        }
    }
    // the new call returned nowhere before: its return would follow an invocation before it
    assert(!returned_before::<M>(t, i - 1, call)) by {
        if returned_before::<M>(t, i - 1, call) {
            let r = choose|r: int| r < i - 1 && #[trigger] ret_at::<M>(t, r, call);
            let k = choose|k: int| k < r && #[trigger] inv_at::<M>(t, k, call);
        }
    }
    // the calls that took effect were invoked before, so they are not `call`
    assert forall|q: int| 0 <= q < p implies #[trigger] ops[q].call != call by {
        assert(invoked_before::<M>(t, i - 1, ops[q].call));
        let k = choose|k: int| k < i - 1 && #[trigger] inv_at::<M>(t, k, ops[q].call);
        if ops[q].call == call {
            assert(inv_at::<M>(t, k, call));
        }
    }
    assert forall|q: int| 0 <= q < p implies #[trigger] invoked_before::<M>(t, i, ops[q].call) by {
        assert(invoked_before::<M>(t, i - 1, ops[q].call));
    }
    assert forall|q: int| p <= q < ops.len() implies !#[trigger] returned_before::<M>(t, i, ops[q].call) by {
        assert(!returned_before::<M>(t, i - 1, ops[q].call));
    }
    assert forall|x: CallId| #[trigger] d.calls.contains_key(x) <==> (invoked_before::<M>(t, i, x) && !returned_before::<M>(t, i, x)) by {
        if x != call {
            assert(d.calls.contains_key(x) == cfg.calls.contains_key(x));
            assert(cfg.calls.contains_key(x) <==> (invoked_before::<M>(t, i - 1, x) && !returned_before::<M>(t, i - 1, x)));
        }
    }
    assert forall|q: int| 0 <= q < p && #[trigger] d.calls.contains_key(ops[q].call) implies d.calls[ops[q].call] == Call::<M::External, M::Response>::Done(ops[q].resp) by {
        assert(ops[q].call != call);
        assert(cfg.calls.contains_key(ops[q].call));
    }
    assert forall|x: CallId, k: int|
        #[trigger] d.calls.contains_key(x) && #[trigger] inv_at::<M>(t, k, x) && (forall|q: int| 0 <= q < p ==> ops[q].call != x)
            implies d.calls[x] == Call::<M::External, M::Response>::InFlight(t[k]->Invoke_req) by {
        if x == call {
            assert(k == i - 1);
        } else {
            assert(cfg.calls.contains_key(x));
        }
    }
}

/// After a return, by the linearization's call `pos`, already taken effect.
proof fn lemma_built_return<M: Model>(
    m: M,
    t: Seq<Ev<M>>,
    ops: Seq<OpOf<M>>,
    states: Seq<M::State>,
    i: int,
    p: int,
    pos: int,
    cfg: Cfg<M>,
    d: Cfg<M>,
)
    requires
        invoked_once::<M>(t),
        well_formed::<M>(t),
        forall|a: int, b: int| 0 <= a < b < ops.len() ==> #[trigger] ops[a].call != #[trigger] ops[b].call,
        0 < i <= t.len(),
        t[i - 1] is Return,
        0 <= pos < p,
        ops[pos].call == t[i - 1]->Return_call,
        built(m, t, ops, states, i - 1, p, cfg),
        d == (semantics::Config { calls: cfg.calls.remove(t[i - 1]->Return_call), ..cfg }),
    ensures
        built(m, t, ops, states, i, p, d),
{
    let call = t[i - 1]->Return_call;
    assert(ret_at::<M>(t, i - 1, call));
    assert forall|x: CallId| #[trigger] invoked_before::<M>(t, i, x) <==> invoked_before::<M>(t, i - 1, x) by {
        if invoked_before::<M>(t, i, x) {
            let k = choose|k: int| k < i && #[trigger] inv_at::<M>(t, k, x);
            assert(k != i - 1);
        }
        if invoked_before::<M>(t, i - 1, x) {
            let k = choose|k: int| k < i - 1 && #[trigger] inv_at::<M>(t, k, x);
            assert(k < i);
        }
    }
    assert forall|x: CallId| #[trigger] returned_before::<M>(t, i, x) <==> (returned_before::<M>(t, i - 1, x) || x == call) by {
        if returned_before::<M>(t, i, x) {
            let k = choose|k: int| k < i && #[trigger] ret_at::<M>(t, k, x);
            if k < i - 1 {
                assert(returned_before::<M>(t, i - 1, x));
            }
        }
        if returned_before::<M>(t, i - 1, x) {
            let k = choose|k: int| k < i - 1 && #[trigger] ret_at::<M>(t, k, x);
            assert(k < i);
        }
    }
    assert forall|q: int| 0 <= q < p implies #[trigger] invoked_before::<M>(t, i, ops[q].call) by {
        assert(invoked_before::<M>(t, i - 1, ops[q].call));
    }
    assert forall|q: int| p <= q < ops.len() implies !#[trigger] returned_before::<M>(t, i, ops[q].call) by {
        assert(!returned_before::<M>(t, i - 1, ops[q].call));
        assert(ops[pos].call != ops[q].call);
    }
    assert forall|x: CallId| #[trigger] d.calls.contains_key(x) <==> (invoked_before::<M>(t, i, x) && !returned_before::<M>(t, i, x)) by {
        if x != call {
            assert(d.calls.contains_key(x) == cfg.calls.contains_key(x));
            assert(cfg.calls.contains_key(x) <==> (invoked_before::<M>(t, i - 1, x) && !returned_before::<M>(t, i - 1, x)));
        }
    }
    assert forall|q: int| 0 <= q < p && #[trigger] d.calls.contains_key(ops[q].call) implies d.calls[ops[q].call] == Call::<M::External, M::Response>::Done(ops[q].resp) by {
        assert(cfg.calls.contains_key(ops[q].call));
    }
    assert forall|x: CallId, k: int|
        #[trigger] d.calls.contains_key(x) && #[trigger] inv_at::<M>(t, k, x) && (forall|q: int| 0 <= q < p ==> ops[q].call != x)
            implies d.calls[x] == Call::<M::External, M::Response>::InFlight(t[k]->Invoke_req) by {
        assert(cfg.calls.contains_key(x));
    }
}

/// After the linearization's call `p` takes effect.
proof fn lemma_built_effect<M: Model>(m: M, t: Seq<Ev<M>>, ops: Seq<OpOf<M>>, states: Seq<M::State>, i: int, p: int, cfg: Cfg<M>, d: Cfg<M>)
    requires
        forall|a: int, b: int| 0 <= a < b < ops.len() ==> #[trigger] ops[a].call != #[trigger] ops[b].call,
        built(m, t, ops, states, i, p, cfg),
        p < ops.len(),
        invoked_before::<M>(t, i, ops[p].call),
        cfg.calls.contains_key(ops[p].call),
        d.state == states[p + 1],
        d.calls == cfg.calls.insert(ops[p].call, Call::Done(ops[p].resp)),
        d.work == cfg.work,
        d.sent == cfg.sent,
    ensures
        built(m, t, ops, states, i, p + 1, d),
{
    let c = ops[p].call;
    assert forall|q: int| 0 <= q < p + 1 implies #[trigger] invoked_before::<M>(t, i, ops[q].call) by {}
    assert forall|x: CallId| #[trigger] d.calls.contains_key(x) <==> (invoked_before::<M>(t, i, x) && !returned_before::<M>(t, i, x)) by {
        assert(d.calls.contains_key(x) == cfg.calls.contains_key(x));
    }
    assert forall|q: int| 0 <= q < p + 1 && #[trigger] d.calls.contains_key(ops[q].call) implies d.calls[ops[q].call] == Call::<M::External, M::Response>::Done(ops[q].resp) by {
        if q < p {
            assert(ops[q].call != c);
            assert(cfg.calls.contains_key(ops[q].call));
        }
    }
    assert forall|x: CallId, k: int|
        #[trigger] d.calls.contains_key(x) && #[trigger] inv_at::<M>(t, k, x) && (forall|q: int| 0 <= q < p + 1 ==> ops[q].call != x)
            implies d.calls[x] == Call::<M::External, M::Response>::InFlight(t[k]->Invoke_req) by {
        assert(x != c);
        assert(cfg.calls.contains_key(x));
        assert(forall|q: int| 0 <= q < p ==> ops[q].call != x);
    }
}

} // verus!
