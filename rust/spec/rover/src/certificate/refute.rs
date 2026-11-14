//! Refutation: a proof that no execution shows a trace.
//!
//! [`certify`](super::certify) shows a trace valid by replaying one execution.
//! Showing a trace invalid means accounting for every execution, so
//! [`refute`] doesn't search: it enumerates. From the initial configuration it
//! takes every silent step there is, again and again, until the set of
//! configurations is closed under them; then it maps every configuration
//! through every way the next event can be observed, closes again, and so on.
//! If at some event no configuration can show it, no execution shows the
//! trace. That is the theorem `refute` is verified against: an answer
//! `Some(k)` means `!valid(m, init, trace)`.
//!
//! Nothing here depends on a particular model: the proof is about the
//! [`Model`] trait and [`semantics`], and needs only what `certify` needs (a
//! model's methods compute their spec twins; `Clone` copies and `PartialEq`
//! compares). In particular it doesn't use footprints or partitions: it never
//! leaves a step out, so a wrong footprint can't make it wrong.
//!
//! It is exhaustive, so it is slow: run it on the shortest prefix the fast
//! checker rejects. `limit` bounds each set of configurations; past it, the
//! answer is `None`, as it is for a trace it can't refute.

#![allow(unused_imports)]

use vstd::prelude::*;

use super::trusted::{copy, same};
use super::{Config, EventOf, Silent};
use crate::semantics::{self, Call, Cfg, Ev, Execution, Label};
use crate::{CallId, Event, Model};

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

// ------------------------------------------------------------- what is shown

/// Some legal execution from the initial configuration shows the first `k`
/// events of the trace and ends in `c`.
pub open spec fn reach<M: Model>(m: M, init: M::State, trace: Seq<Ev<M>>, k: int, c: Cfg<M>) -> bool {
    exists|steps: Execution<M>|
        #![trigger semantics::legal(m, semantics::initial::<M>(init), steps), semantics::project::<M>(steps)]
        semantics::legal(m, semantics::initial::<M>(init), steps) && semantics::project::<M>(steps) == trace.subrange(0, k)
            && semantics::before::<M>(semantics::initial::<M>(init), steps, steps.len() as int) == c
}

/// `c` is one of the configurations in `set`.
pub open spec fn in_set<'m, M: Model>(set: Seq<Config<'m, M>>, c: Cfg<M>) -> bool {
    exists|q: int| #![trigger set[q]] 0 <= q < set.len() && set[q]@ == c
}

/// Every configuration some execution showing the first `k` events ends in is
/// in `set`.
pub open spec fn covers<'m, M: Model>(m: M, init: M::State, trace: Seq<Ev<M>>, k: int, set: Seq<Config<'m, M>>) -> bool {
    forall|c: Cfg<M>| #[trigger] reach(m, init, trace, k, c) ==> in_set(set, c)
}

/// Every call in flight or answered in `c` is among `ids`.
pub open spec fn keys_in<M: Model>(c: Cfg<M>, ids: Seq<CallId>) -> bool {
    forall|call: CallId| #[trigger] c.calls.contains_key(call) ==> ids.contains(call)
}

/// `ids` has every call the trace invokes.
pub open spec fn invoked<M: Model>(trace: Seq<Ev<M>>, ids: Seq<CallId>) -> bool {
    forall|i: int| 0 <= i < trace.len() ==> (#[trigger] trace[i] matches Event::Invoke { call, .. } ==> ids.contains(call))
}

/// Every call an observed step of the execution invokes is among `ids`.
pub open spec fn labels_in<M: Model>(steps: Execution<M>, ids: Seq<CallId>) -> bool {
    forall|i: int| 0 <= i < steps.len() ==> (#[trigger] steps[i].0 matches Label::Obs(Event::Invoke { call, .. }) ==> ids.contains(call))
}

/// Every silent step from a configuration in `set` leads to one in `set`
/// (for configurations whose calls are among `ids`, which every reachable
/// one's are).
pub open spec fn closed<'m, M: Model>(m: M, set: Seq<Config<'m, M>>, ids: Seq<CallId>) -> bool {
    forall|i: int, d: Cfg<M>|
        #![trigger set[i], semantics::step(m, set[i]@, Label::Silent, d)]
        0 <= i < set.len() && keys_in::<M>(set[i]@, ids) && semantics::step(m, set[i]@, Label::Silent, d) ==> in_set(set, d)
}

/// `big` keeps what `small` has, in place, and maybe more after it.
pub open spec fn grows<'m, M: Model>(small: Seq<Config<'m, M>>, big: Seq<Config<'m, M>>) -> bool {
    big.len() >= small.len() && forall|q: int| 0 <= q < small.len() ==> #[trigger] big[q] == small[q]
}

// ----------------------------------------------------------------- the check

/// `Some(k)`: no execution of the system shows `trace`; none can show its
/// `k`-th event after the ones before it. `None`: can't tell (the trace may be
/// valid, or a set of configurations outgrew `limit`).
///
/// Verified: `Some(_)` means the trace is not valid.
pub fn refute<M: Model>(m: &M, init: M::State, trace: &[EventOf<M>], limit: usize) -> (r: Option<usize>)
    ensures
        r matches Some(k) ==> k < trace@.len() && !semantics::valid(*m, init, trace@),
{
    let ids = invoked_ids::<M>(trace);
    let mut start: Vec<Config<M>> = Vec::new();
    start.push(Config::initial(m, init));
    let mut set = match close(m, start, &ids, limit) {
        Some(s) => s,
        None => return None,
    };
    proof {
        assert(set@[0]@ == semantics::initial::<M>(init));
        lemma_covers_start(*m, init, trace@, set@, ids@);
    }
    for k in 0..trace.len()
        invariant
            forall|q: int| 0 <= q < set@.len() ==> #[trigger] set@[q].m == m,
            closed(*m, set@, ids@),
            covers(*m, init, trace@, k as int, set@),
            invoked::<M>(trace@, ids@),
    {
        let mut next: Vec<Config<M>> = Vec::new();
        let mut index = Index::new();
        for i in 0..set.len()
            invariant
                k < trace@.len(),
                forall|q: int| 0 <= q < set@.len() ==> #[trigger] set@[q].m == m,
                forall|q: int| 0 <= q < next@.len() ==> #[trigger] next@[q].m == m,
                forall|i2: int, d: Cfg<M>|
                    #![trigger set@[i2], semantics::step(*m, set@[i2]@, Label::Obs(trace@[k as int]), d)]
                    0 <= i2 < i && semantics::step(*m, set@[i2]@, Label::Obs(trace@[k as int]), d) ==> in_set(next@, d),
        {
            let succ = obs_succs(&set[i], &trace[k]);
            let ghost before_add = next@;
            for t in 0..succ.len()
                invariant
                    forall|q: int| 0 <= q < next@.len() ==> #[trigger] next@[q].m == m,
                    forall|q: int| 0 <= q < succ@.len() ==> #[trigger] succ@[q].m == m,
                    grows(before_add, next@),
                    forall|t2: int| 0 <= t2 < t ==> in_set(next@, #[trigger] succ@[t2]@),
            {
                let ghost was = next@;
                if !add(&mut next, &mut index, dup(&succ[t]), limit) {
                    return None;
                }
                proof {
                    assert forall|t2: int| 0 <= t2 < t implies in_set(next@, #[trigger] succ@[t2]@) by {
                        lemma_in_set_grows(was, next@, succ@[t2]@);
                    }
                }
            }
            proof {
                assert forall|i2: int, d: Cfg<M>|
                    #![trigger set@[i2], semantics::step(*m, set@[i2]@, Label::Obs(trace@[k as int]), d)]
                    0 <= i2 <= i && semantics::step(*m, set@[i2]@, Label::Obs(trace@[k as int]), d) implies in_set(next@, d) by {
                    if i2 < i {
                        lemma_in_set_grows(before_add, next@, d);
                    } else {
                        assert(set@[i2].m == m);
                        assert(semantics::step(*set@[i2].m, set@[i2]@, Label::Obs(trace@[k as int]), d));
                        assert(in_set(succ@, d));
                        let q = choose|q: int| #![trigger succ@[q]] 0 <= q < succ@.len() && succ@[q]@ == d;
                        assert(in_set(next@, succ@[q]@));
                    }
                }
            }
        }
        if next.len() == 0 {
            proof {
                lemma_stuck(*m, init, trace@, k as int, set@, next@);
            }
            return Some(k);
        }
        let ghost entered = next@;
        set = match close(m, next, &ids, limit) {
            Some(s) => s,
            None => return None,
        };
        proof {
            lemma_covers_next(*m, init, trace@, k as int, ids@, entered, set@);
            assert forall|c: Cfg<M>| #[trigger] reach(*m, init, trace@, k + 1, c) implies in_set(set@, c) by {}
        }
    }
    None
}

// ----------------------------------------------- the sets, and growing them

/// Every call id the trace invokes.
fn invoked_ids<M: Model>(trace: &[EventOf<M>]) -> (ids: Vec<CallId>)
    ensures
        invoked::<M>(trace@, ids@),
{
    let mut ids: Vec<CallId> = Vec::new();
    for i in 0..trace.len()
        invariant
            forall|i2: int| 0 <= i2 < i ==> (#[trigger] trace@[i2] matches Event::Invoke { call, .. } ==> ids@.contains(call)),
    {
        let ghost was = ids@;
        if let Event::Invoke { call, .. } = &trace[i] {
            ids.push(*call);
            proof {
                assert(ids@[ids@.len() - 1] == *call);
            }
        }
        proof {
            assert forall|i2: int| 0 <= i2 <= i implies (#[trigger] trace@[i2] matches Event::Invoke { call, .. } ==> ids@.contains(call)) by {
                if i2 < i {
                    if let Event::Invoke { call, .. } = trace@[i2] {
                        let p = choose|p: int| 0 <= p < was.len() && was[p] == call;
                        assert(ids@[p] == call);
                    }
                }
            }
        }
    }
    ids
}

/// A copy.
fn dup<'m, M: Model>(c: &Config<'m, M>) -> (r: Config<'m, M>)
    ensures
        r@ == c@,
        r.m == c.m,
{
    Config { m: c.m, state: copy(&c.state), calls: copy(&c.calls), work: copy(&c.work), sent: copy(&c.sent) }
}

/// The same configuration (`false` may still be the same: then it is kept
/// twice, which costs time, not soundness).
fn same_config<'m, M: Model>(a: &Config<'m, M>, b: &Config<'m, M>) -> (r: bool)
    ensures
        r ==> a@ == b@,
{
    same(&a.state, &b.state) && same(&a.calls, &b.calls) && same(&a.work, &b.work) && same(&a.sent, &b.sent)
}

/// Adds `d` to `set` unless it is there. `false`: it isn't, and `set` has
/// `limit` configurations already. `index` only suggests where `d` might be;
/// it is checked, so a wrong suggestion costs a duplicate, never soundness.
fn add<'m, M: Model>(set: &mut Vec<Config<'m, M>>, index: &mut Index, d: Config<'m, M>, limit: usize) -> (ok: bool)
    ensures
        grows(old(set)@, final(set)@),
        final(set)@.len() <= old(set)@.len() + 1,
        final(set)@.len() == old(set)@.len() + 1 ==> final(set)@[old(set)@.len() as int] == d && old(set)@.len() < limit,
        ok ==> in_set(final(set)@, d@),
{
    let hint = index.candidates(&d);
    for h in 0..hint.len() {
        let q = hint[h];
        if q < set.len() && same_config(&set[q], &d) {
            proof {
                assert(set@[q as int]@ == d@);
            }
            return true;
        }
    }
    if set.len() >= limit {
        return false;
    }
    index.insert(&d, set.len());
    set.push(d);
    proof {
        assert(set@[set@.len() - 1]@ == d@);
    }
    true
}

/// Where in a set a configuration might be, by a hash of it. Not trusted:
/// nothing is assumed about what it answers.
#[verifier::external_body]
pub(crate) struct Index {
    at: std::collections::HashMap<u64, Vec<usize>>,
}

impl Index {
    #[verifier::external_body]
    fn new() -> Index {
        Index { at: std::collections::HashMap::new() }
    }

    /// Positions where `c` might be.
    #[verifier::external_body]
    fn candidates<'m, M: Model>(&self, c: &Config<'m, M>) -> Vec<usize> {
        self.at.get(&fingerprint(c)).cloned().unwrap_or_default()
    }

    /// `c` is at position `q`.
    #[verifier::external_body]
    fn insert<'m, M: Model>(&mut self, c: &Config<'m, M>, q: usize) {
        self.at.entry(fingerprint(c)).or_default().push(q);
    }
}

/// A hash of a configuration (its calls in call order).
#[verifier::external_body]
fn fingerprint<'m, M: Model>(c: &Config<'m, M>) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    c.state.hash(&mut h);
    let mut calls: Vec<_> = c.calls.iter().collect();
    calls.sort_by_key(|(k, _)| **k);
    for (k, v) in calls {
        k.hash(&mut h);
        match v {
            Call::InFlight(x) => (0u8, x).hash(&mut h),
            Call::Done(r) => (1u8, r).hash(&mut h),
        }
    }
    for w in &c.work {
        (&w.req, w.after, w.due, w.must).hash(&mut h);
    }
    c.sent.hash(&mut h);
    h.finish()
}

/// `set`, grown until every silent step from one of its configurations leads
/// to one of them. `None`: it outgrew `limit`.
#[allow(unused_variables)] // `m` and `bound` appear only in the proof
fn close<'m, M: Model>(m: &'m M, set: Vec<Config<'m, M>>, ids: &Vec<CallId>, limit: usize) -> (r: Option<Vec<Config<'m, M>>>)
    requires
        forall|q: int| 0 <= q < set@.len() ==> #[trigger] set@[q].m == m,
    ensures
        r matches Some(s) ==> {
            &&& forall|q: int| 0 <= q < s@.len() ==> #[trigger] s@[q].m == m
            &&& grows(set@, s@)
            &&& closed(*m, s@, ids@)
        },
{
    let ghost entered = set@;
    let bound = if set.len() > limit { set.len() } else { limit };
    let mut s = set;
    let mut index = Index::new();
    for q in 0..s.len() {
        index.insert(&s[q], q);
    }
    let mut w: usize = 0;
    while w < s.len()
        invariant
            forall|q: int| 0 <= q < s@.len() ==> #[trigger] s@[q].m == m,
            grows(entered, s@),
            w <= s@.len() <= bound,
            bound >= limit,
            forall|i: int, d: Cfg<M>|
                #![trigger s@[i], semantics::step(*m, s@[i]@, Label::Silent, d)]
                0 <= i < w && keys_in::<M>(s@[i]@, ids@) && semantics::step(*m, s@[i]@, Label::Silent, d) ==> in_set(s@, d),
        decreases bound - w,
    {
        let succ = silent_succs(&s[w], ids);
        let ghost at_w = s@;
        for t in 0..succ.len()
            invariant
                forall|q: int| 0 <= q < s@.len() ==> #[trigger] s@[q].m == m,
                forall|q: int| 0 <= q < succ@.len() ==> #[trigger] succ@[q].m == m,
                grows(at_w, s@),
                grows(entered, s@),
                w < at_w.len(),
                s@.len() <= bound,
                bound >= limit,
                forall|t2: int| 0 <= t2 < t ==> in_set(s@, #[trigger] succ@[t2]@),
        {
            let ghost was = s@;
            if !add(&mut s, &mut index, dup(&succ[t]), limit) {
                return None;
            }
            proof {
                assert forall|t2: int| 0 <= t2 < t implies in_set(s@, #[trigger] succ@[t2]@) by {
                    lemma_in_set_grows(was, s@, succ@[t2]@);
                }
                assert(forall|q: int| 0 <= q < entered.len() ==> #[trigger] s@[q] == entered[q]);
                assert(forall|q: int| 0 <= q < at_w.len() ==> #[trigger] s@[q] == at_w[q]);
            }
        }
        proof {
            assert forall|i: int, d: Cfg<M>|
                #![trigger s@[i], semantics::step(*m, s@[i]@, Label::Silent, d)]
                0 <= i <= w && keys_in::<M>(s@[i]@, ids@) && semantics::step(*m, s@[i]@, Label::Silent, d) implies in_set(s@, d) by {
                assert(s@[i] == at_w[i]);
                if i < w {
                    lemma_in_set_grows(at_w, s@, d);
                } else {
                    assert(at_w[i].m == m);
                    assert(semantics::step(*at_w[i].m, at_w[i]@, Label::Silent, d));
                    assert(keys_in::<M>(at_w[i]@, ids@));
                    assert(in_set(succ@, d));
                    let q = choose|q: int| #![trigger succ@[q]] 0 <= q < succ@.len() && succ@[q]@ == d;
                    assert(in_set(s@, succ@[q]@));
                }
            }
        }
        w = w + 1;
    }
    Some(s)
}

// ------------------------------------------------- every step there is

/// Call `call` taking effect with outcome `j`, if it can.
fn effect_at<'m, M: Model>(c: &Config<'m, M>, call: CallId, j: usize) -> (r: Option<Config<'m, M>>)
    ensures
        r matches Some(d) ==> d@ == semantics::effect_next(*c.m, c@, call, j as int) && d.m == c.m,
        r is None ==> !semantics::effect_ok(*c.m, c@, call, j as int),
{
    let mut d = dup(c);
    match d.silent(Silent::Effect { call, j }) {
        Ok(()) => Some(d),
        Err(()) => None,
    }
}

/// Work `i` running with outcome `j`, if it can.
fn run_at<'m, M: Model>(c: &Config<'m, M>, i: usize, j: usize) -> (r: Option<Config<'m, M>>)
    ensures
        r matches Some(d) ==> d@ == semantics::run_next(*c.m, c@, i as int, j as int) && d.m == c.m,
        r is None ==> !semantics::run_ok(*c.m, c@, i as int, j as int),
{
    let mut d = dup(c);
    match d.silent(Silent::Run { i, j }) {
        Ok(()) => Some(d),
        Err(()) => None,
    }
}

/// Every configuration one silent step from `c` leads to (when `c`'s calls are
/// among `ids`).
fn silent_succs<'m, M: Model>(c: &Config<'m, M>, ids: &Vec<CallId>) -> (r: Vec<Config<'m, M>>)
    ensures
        forall|q: int| 0 <= q < r@.len() ==> #[trigger] r@[q].m == c.m,
        forall|d: Cfg<M>|
            #[trigger] semantics::step(*c.m, c@, Label::Silent, d) && keys_in::<M>(c@, ids@) ==> in_set(r@, d),
{
    let mut out: Vec<Config<'m, M>> = Vec::new();
    for a in 0..ids.len()
        invariant
            forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q].m == c.m,
            forall|a2: int, j: int|
                0 <= a2 < a && #[trigger] semantics::effect_ok(*c.m, c@, ids@[a2], j)
                    ==> in_set(out@, semantics::effect_next(*c.m, c@, ids@[a2], j)),
    {
        let call = ids[a];
        let n = match c.calls.get(&call) {
            Some(Call::InFlight(req)) => c.m.external(req, &c.state).len(),
            _ => 0,
        };
        let ghost at_a = out@;
        for j in 0..n
            invariant
                forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q].m == c.m,
                grows(at_a, out@),
                call == ids@[a as int],
                forall|j2: int|
                    0 <= j2 < j && #[trigger] semantics::effect_ok(*c.m, c@, call, j2)
                        ==> in_set(out@, semantics::effect_next(*c.m, c@, call, j2)),
        {
            let ghost was = out@;
            if let Some(d) = effect_at(c, call, j) {
                out.push(d);
                proof {
                    assert(out@[out@.len() - 1]@ == semantics::effect_next(*c.m, c@, call, j as int));
                }
            }
            proof {
                assert forall|j2: int|
                    0 <= j2 <= j && #[trigger] semantics::effect_ok(*c.m, c@, call, j2)
                        implies in_set(out@, semantics::effect_next(*c.m, c@, call, j2)) by {
                    if j2 < j {
                        lemma_in_set_grows(was, out@, semantics::effect_next(*c.m, c@, call, j2));
                    }
                }
            }
        }
        proof {
            assert forall|a2: int, j: int|
                0 <= a2 <= a && #[trigger] semantics::effect_ok(*c.m, c@, ids@[a2], j)
                    implies in_set(out@, semantics::effect_next(*c.m, c@, ids@[a2], j)) by {
                if a2 < a {
                    lemma_in_set_grows(at_a, out@, semantics::effect_next(*c.m, c@, ids@[a2], j));
                } else {
                    assert(j < n);
                }
            }
        }
    }
    let ghost after_effects = out@;
    for i in 0..c.work.len()
        invariant
            forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q].m == c.m,
            grows(after_effects, out@),
            forall|i2: int, j: int|
                0 <= i2 < i && #[trigger] semantics::run_ok(*c.m, c@, i2, j)
                    ==> in_set(out@, semantics::run_next(*c.m, c@, i2, j)),
    {
        let n = c.m.internal(&c.work[i].req, &c.state).len();
        let ghost at_i = out@;
        for j in 0..n
            invariant
                forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q].m == c.m,
                grows(at_i, out@),
                grows(after_effects, out@),
                i < c.work@.len(),
                n == c.m.spec_internal(c@.work[i as int].req, c@.state).len(),
                forall|j2: int|
                    0 <= j2 < j && #[trigger] semantics::run_ok(*c.m, c@, i as int, j2)
                        ==> in_set(out@, semantics::run_next(*c.m, c@, i as int, j2)),
        {
            let ghost was = out@;
            if let Some(d) = run_at(c, i, j) {
                out.push(d);
                proof {
                    assert(out@[out@.len() - 1]@ == semantics::run_next(*c.m, c@, i as int, j as int));
                }
            }
            proof {
                assert forall|j2: int|
                    0 <= j2 <= j && #[trigger] semantics::run_ok(*c.m, c@, i as int, j2)
                        implies in_set(out@, semantics::run_next(*c.m, c@, i as int, j2)) by {
                    if j2 < j {
                        lemma_in_set_grows(was, out@, semantics::run_next(*c.m, c@, i as int, j2));
                    }
                }
                assert(forall|q: int| 0 <= q < after_effects.len() ==> #[trigger] out@[q] == after_effects[q]);
            }
        }
        proof {
            assert forall|i2: int, j: int|
                0 <= i2 <= i && #[trigger] semantics::run_ok(*c.m, c@, i2, j)
                    implies in_set(out@, semantics::run_next(*c.m, c@, i2, j)) by {
                if i2 < i {
                    lemma_in_set_grows(at_i, out@, semantics::run_next(*c.m, c@, i2, j));
                }
            }
        }
    }
    proof {
        assert forall|d: Cfg<M>|
            #[trigger] semantics::step(*c.m, c@, Label::Silent, d) && keys_in::<M>(c@, ids@) implies in_set(out@, d) by {
            lemma_silent_cases(*c.m, c@, d);
            if exists|call: CallId, j: int| #[trigger] semantics::effect_ok(*c.m, c@, call, j) && d == semantics::effect_next(*c.m, c@, call, j) {
                let (call, j) = choose|call: CallId, j: int|
                    #[trigger] semantics::effect_ok(*c.m, c@, call, j) && d == semantics::effect_next(*c.m, c@, call, j);
                assert(c@.calls.contains_key(call));
                assert(ids@.contains(call));
                let a2 = choose|a2: int| 0 <= a2 < ids@.len() && ids@[a2] == call;
                assert(semantics::effect_ok(*c.m, c@, ids@[a2], j));
                lemma_in_set_grows(after_effects, out@, d);
            }
        }
    }
    out
}

/// Every configuration observing `e` from `c` leads to.
fn obs_succs<'m, M: Model>(c: &Config<'m, M>, e: &EventOf<M>) -> (r: Vec<Config<'m, M>>)
    ensures
        forall|q: int| 0 <= q < r@.len() ==> #[trigger] r@[q].m == c.m,
        forall|d: Cfg<M>| #[trigger] semantics::step(*c.m, c@, Label::Obs(*e), d) ==> in_set(r@, d),
{
    let mut out: Vec<Config<'m, M>> = Vec::new();
    if c.overdue() {
        return out;
    }
    match e {
        Event::Invoke { call, req } => {
            if !c.calls.contains_key(call) {
                let mut d = dup(c);
                d.calls.insert(*call, Call::InFlight(copy(req)));
                out.push(d);
                proof {
                    assert(out@[0]@ == (semantics::Config { calls: c@.calls.insert(*call, Call::InFlight(*req)), ..c@ }));
                }
            }
        }
        Event::Return { call, res } => {
            if let Some(Call::Done(expected)) = c.calls.get(call) {
                if same(expected, res) {
                    let mut d = dup(c);
                    d.calls.remove(call);
                    out.push(d);
                    proof {
                        assert(out@[0]@ == (semantics::Config { calls: c@.calls.remove(*call), ..c@ }));
                    }
                }
            }
        }
        Event::Receive { msg } => {
            for i in 0..c.sent.len()
                invariant
                    forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q].m == c.m,
                    !semantics::overdue(*c.m, c@),
                    forall|i2: int|
                        0 <= i2 < i && #[trigger] c@.sent[i2] == *msg
                            ==> in_set(out@, semantics::Config { sent: c@.sent.remove(i2), ..c@ }),
            {
                let ghost was = out@;
                if same(&c.sent[i], msg) {
                    let mut d = dup(c);
                    d.sent.remove(i);
                    out.push(d);
                    proof {
                        assert(out@[out@.len() - 1]@ == (semantics::Config { sent: c@.sent.remove(i as int), ..c@ }));
                    }
                }
                proof {
                    assert forall|i2: int|
                        0 <= i2 <= i && #[trigger] c@.sent[i2] == *msg
                            implies in_set(out@, semantics::Config { sent: c@.sent.remove(i2), ..c@ }) by {
                        if i2 < i {
                            lemma_in_set_grows(was, out@, semantics::Config { sent: c@.sent.remove(i2), ..c@ });
                        }
                    }
                }
            }
        }
    }
    proof {
        assert forall|d: Cfg<M>| #[trigger] semantics::step(*c.m, c@, Label::Obs(*e), d) implies in_set(out@, d) by {
            match *e {
                Event::Invoke { call, req } => {
                    assert(semantics::invoke(*c.m, c@, Label::Obs(*e), d));
                    assert(out@[0]@ == d);
                }
                Event::Return { call, res } => {
                    assert(semantics::ret(*c.m, c@, Label::Obs(*e), d));
                    assert(out@[0]@ == d);
                }
                Event::Receive { msg } => {
                    assert(semantics::receive(*c.m, c@, Label::Obs(*e), d));
                    let i2 = choose|i2: int| 0 <= i2 < c@.sent.len() && #[trigger] c@.sent[i2] == msg
                        && d == (semantics::Config { sent: c@.sent.remove(i2), ..c@ });
                }
            }
        }
    }
    out
}

// ------------------------------------------------------------------ lemmas

proof fn lemma_in_set_grows<'m, M: Model>(small: Seq<Config<'m, M>>, big: Seq<Config<'m, M>>, c: Cfg<M>)
    requires
        grows(small, big),
        in_set(small, c),
    ensures
        in_set(big, c),
{
    let q = choose|q: int| #![trigger small[q]] 0 <= q < small.len() && small[q]@ == c;
    assert(big[q] == small[q]);
}

/// A silent step is a call taking effect or work running.
proof fn lemma_silent_cases<M: Model>(m: M, c: Cfg<M>, d: Cfg<M>)
    requires
        semantics::step(m, c, Label::Silent, d),
    ensures
        (exists|call: CallId, j: int| #[trigger] semantics::effect_ok(m, c, call, j) && d == semantics::effect_next(m, c, call, j))
            || (exists|i: int, j: int| #[trigger] semantics::run_ok(m, c, i, j) && d == semantics::run_next(m, c, i, j)),
{
    if semantics::effect(m, c, Label::Silent, d) {
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
        assert(semantics::effect_ok(m, c, call, j) && d == semantics::effect_next(m, c, call, j));
    } else {
        assert(semantics::run(m, c, Label::Silent, d));
        let (i, j) = choose|i: int, j: int|
            #![trigger c.work[i], m.spec_internal(c.work[i].req, c.state)[j]]
            0 <= i < c.work.len() && c.work[i].after <= semantics::clock(m, c) && (semantics::overdue(m, c) ==> semantics::is_first(m, c, i)) && {
                let outs = m.spec_internal(c.work[i].req, c.state);
                0 <= j < outs.len() && d == semantics::Config {
                    state: outs[j].next,
                    work: semantics::start_all(c.work.remove(i), outs[j].work, m.spec_now(outs[j].next)),
                    sent: c.sent + outs[j].send,
                    ..c
                }
            };
        assert(semantics::run_ok(m, c, i, j) && d == semantics::run_next(m, c, i, j));
    }
}

/// A prefix of a legal execution is legal, through the same configurations.
proof fn lemma_prefix<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>, n: int)
    requires
        semantics::legal(m, first, steps),
        0 <= n <= steps.len(),
    ensures
        semantics::legal(m, first, steps.subrange(0, n)),
        forall|i: int| 0 <= i <= n ==> #[trigger] semantics::before::<M>(first, steps.subrange(0, n), i) == semantics::before::<M>(first, steps, i),
{
    let pre = steps.subrange(0, n);
    assert forall|i: int| 0 <= i <= n implies #[trigger] semantics::before::<M>(first, pre, i) == semantics::before::<M>(first, steps, i) by {
        if i > 0 {
            assert(pre[i - 1] == steps[i - 1]);
        }
    }
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] semantics::step(m, semantics::before::<M>(first, pre, i), pre[i].0, pre[i].1) by {
        assert(semantics::before::<M>(first, pre, i) == semantics::before::<M>(first, steps, i));
        assert(semantics::step(m, semantics::before::<M>(first, steps, i), steps[i].0, steps[i].1));
    }
}

/// The projection of a prefix of the steps is a prefix of the projection.
proof fn lemma_project_prefix<M: Model>(steps: Execution<M>, n: int)
    requires
        0 <= n <= steps.len(),
    ensures
        semantics::project::<M>(steps.subrange(0, n)).len() <= semantics::project::<M>(steps).len(),
        semantics::project::<M>(steps.subrange(0, n))
            == semantics::project::<M>(steps).subrange(0, semantics::project::<M>(steps.subrange(0, n)).len() as int),
    decreases steps.len(),
{
    if n == steps.len() {
        assert(steps.subrange(0, n) =~= steps);
    } else {
        let s = steps.drop_last();
        lemma_project_prefix::<M>(s, n);
        assert(steps.subrange(0, n) =~= s.subrange(0, n));
        let ps = semantics::project::<M>(s);
        let pn = semantics::project::<M>(s.subrange(0, n));
        assert(pn == ps.subrange(0, pn.len() as int));
        match steps.last().0 {
            Label::Obs(e) => {
                assert(semantics::project::<M>(steps) == ps.push(e));
                assert(ps.push(e).subrange(0, pn.len() as int) =~= ps.subrange(0, pn.len() as int));
            }
            Label::Silent => {}
        }
    }
}

/// An execution showing `k + 1` events: the step showing the last of them,
/// the steps before it showing the first `k`, and only silent steps after.
proof fn lemma_split<M: Model>(steps: Execution<M>, k: int) -> (n: int)
    requires
        k >= 0,
        semantics::project::<M>(steps).len() == k + 1,
    ensures
        0 <= n < steps.len(),
        steps[n].0 == Label::<_, _, _>::Obs(semantics::project::<M>(steps)[k]),
        semantics::project::<M>(steps.subrange(0, n)) == semantics::project::<M>(steps).subrange(0, k),
        forall|i: int| n < i < steps.len() ==> #[trigger] steps[i].0 is Silent,
    decreases steps.len(),
{
    let s = steps.drop_last();
    assert(steps.len() > 0);
    match steps.last().0 {
        Label::Obs(e) => {
            let n = steps.len() - 1;
            assert(steps.subrange(0, n) =~= s);
            assert(semantics::project::<M>(steps) == semantics::project::<M>(s).push(e));
            assert(semantics::project::<M>(s) =~= semantics::project::<M>(steps).subrange(0, k));
            n
        }
        Label::Silent => {
            assert(semantics::project::<M>(steps) == semantics::project::<M>(s));
            let n = lemma_split::<M>(s, k);
            assert(steps.subrange(0, n) =~= s.subrange(0, n));
            assert(steps[n] == s[n]);
            assert forall|i: int| n < i < steps.len() implies #[trigger] steps[i].0 is Silent by {
                if i < steps.len() - 1 {
                    assert(steps[i] == s[i]);
                    assert(s[i].0 is Silent);
                }
            }
            n
        }
    }
}

/// An execution showing more than `k` events has a prefix showing exactly the
/// first `k + 1`.
proof fn lemma_prefix_showing<M: Model>(steps: Execution<M>, k: int) -> (n: int)
    requires
        0 <= k < semantics::project::<M>(steps).len(),
    ensures
        0 <= n <= steps.len(),
        semantics::project::<M>(steps.subrange(0, n)) == semantics::project::<M>(steps).subrange(0, k + 1),
    decreases steps.len(),
{
    let s = steps.drop_last();
    let ps = semantics::project::<M>(s);
    assert(steps.len() > 0);
    match steps.last().0 {
        Label::Obs(e) => {
            assert(semantics::project::<M>(steps) == ps.push(e));
            if k < ps.len() {
                let n = lemma_prefix_showing::<M>(s, k);
                assert(steps.subrange(0, n) =~= s.subrange(0, n));
                assert(ps.push(e).subrange(0, k + 1) =~= ps.subrange(0, k + 1));
                n
            } else {
                assert(steps.subrange(0, steps.len() as int) =~= steps);
                assert(ps.push(e).subrange(0, k + 1) =~= ps.push(e));
                steps.len() as int
            }
        }
        Label::Silent => {
            assert(semantics::project::<M>(steps) == ps);
            let n = lemma_prefix_showing::<M>(s, k);
            assert(steps.subrange(0, n) =~= s.subrange(0, n));
            n
        }
    }
}

/// Every event an observed step shows is in the projection.
proof fn lemma_labels_shown<M: Model>(steps: Execution<M>)
    ensures
        forall|i: int| 0 <= i < steps.len() ==> (#[trigger] steps[i].0 matches Label::Obs(e) ==> semantics::project::<M>(steps).contains(e)),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let s = steps.drop_last();
        lemma_labels_shown::<M>(s);
        let ps = semantics::project::<M>(s);
        assert forall|i: int| 0 <= i < steps.len() implies (#[trigger] steps[i].0 matches Label::Obs(e) ==> semantics::project::<M>(steps).contains(e)) by {
            if let Label::Obs(e) = steps[i].0 {
                match steps.last().0 {
                    Label::Obs(f) => {
                        assert(semantics::project::<M>(steps) == ps.push(f));
                        if i < steps.len() - 1 {
                            assert(steps[i] == s[i]);
                            let p = choose|p: int| 0 <= p < ps.len() && ps[p] == e;
                            assert(ps.push(f)[p] == e);
                        } else {
                            assert(ps.push(f)[ps.len() as int] == e);
                        }
                    }
                    Label::Silent => {
                        assert(semantics::project::<M>(steps) == ps);
                        assert(steps[i] == s[i]);
                    }
                }
            }
        }
    }
}

/// An execution showing the first `k` events of a trace invokes only calls
/// the trace invokes.
proof fn lemma_labels_in<M: Model>(steps: Execution<M>, trace: Seq<Ev<M>>, k: int, ids: Seq<CallId>)
    requires
        0 <= k <= trace.len(),
        semantics::project::<M>(steps) == trace.subrange(0, k),
        invoked::<M>(trace, ids),
    ensures
        labels_in::<M>(steps, ids),
{
    lemma_labels_shown::<M>(steps);
    assert forall|i: int| 0 <= i < steps.len() implies (#[trigger] steps[i].0 matches Label::Obs(Event::Invoke { call, .. }) ==> ids.contains(call)) by {
        if let Label::Obs(e) = steps[i].0 {
            if let Event::Invoke { call, .. } = e {
                let p = choose|p: int| 0 <= p < k && trace.subrange(0, k)[p] == e;
                assert(trace[p] == e);
            }
        }
    }
}

/// Along an execution that invokes only calls among `ids`, every
/// configuration's calls are among `ids`.
proof fn lemma_keys<M: Model>(m: M, first: Cfg<M>, steps: Execution<M>, ids: Seq<CallId>, n: int)
    requires
        semantics::legal(m, first, steps),
        keys_in::<M>(first, ids),
        labels_in::<M>(steps, ids),
        0 <= n <= steps.len(),
    ensures
        keys_in::<M>(semantics::before::<M>(first, steps, n), ids),
    decreases n,
{
    if n > 0 {
        lemma_keys(m, first, steps, ids, n - 1);
        let c = semantics::before::<M>(first, steps, n - 1);
        let (l, d) = steps[n - 1];
        assert(semantics::step(m, c, l, d));
        assert(semantics::before::<M>(first, steps, n) == d);
        assert forall|call: CallId| #[trigger] d.calls.contains_key(call) implies ids.contains(call) by {
            if semantics::invoke(m, c, l, d) {
                if let Label::Obs(Event::Invoke { call: x, .. }) = l {
                    if call != x {
                        assert(c.calls.contains_key(call));
                    }
                }
            } else if semantics::ret(m, c, l, d) {
                assert(c.calls.contains_key(call));
            } else if semantics::receive(m, c, l, d) {
                assert(c.calls.contains_key(call));
            } else if semantics::effect(m, c, l, d) {
                let (x, j) = choose|x: CallId, j: int|
                    #![trigger c.calls[x], m.spec_external(c.calls[x]->InFlight_0, c.state)[j]]
                    c.calls.contains_key(x) && c.calls[x] is InFlight && {
                        let outs = m.spec_external(c.calls[x]->InFlight_0, c.state);
                        0 <= j < outs.len() && d == semantics::Config {
                            state: outs[j].next,
                            calls: c.calls.insert(x, Call::Done(outs[j].resp)),
                            work: semantics::start_all(c.work, outs[j].work, m.spec_now(outs[j].next)),
                            sent: c.sent + outs[j].send,
                            ..c
                        }
                    };
                assert(c.calls.contains_key(call));
            } else {
                assert(semantics::run(m, c, l, d));
                assert(c.calls.contains_key(call));
            }
        }
    }
}

/// Silent steps from a configuration in a closed set stay in it.
proof fn lemma_silent_tail<'m, M: Model>(m: M, first: Cfg<M>, steps: Execution<M>, a: int, set: Seq<Config<'m, M>>, ids: Seq<CallId>)
    requires
        semantics::legal(m, first, steps),
        0 <= a <= steps.len(),
        in_set(set, semantics::before::<M>(first, steps, a)),
        closed(m, set, ids),
        forall|i: int| a <= i < steps.len() ==> #[trigger] steps[i].0 is Silent,
        forall|i: int| a <= i <= steps.len() ==> keys_in::<M>(#[trigger] semantics::before::<M>(first, steps, i), ids),
    ensures
        in_set(set, semantics::before::<M>(first, steps, steps.len() as int)),
    decreases steps.len() - a,
{
    if a < steps.len() {
        let c = semantics::before::<M>(first, steps, a);
        let q = choose|q: int| #![trigger set[q]] 0 <= q < set.len() && set[q]@ == c;
        assert(steps[a].0 is Silent);
        assert(semantics::step(m, c, steps[a].0, steps[a].1));
        assert(steps[a].0 == Label::<M::External, M::Response, M::Dispatch>::Silent);
        assert(keys_in::<M>(set[q]@, ids));
        assert(semantics::step(m, set[q]@, Label::Silent, steps[a].1));
        assert(semantics::before::<M>(first, steps, a + 1) == steps[a].1);
        lemma_silent_tail(m, first, steps, a + 1, set, ids);
    }
}

/// The first set covers every configuration the system reaches before
/// showing any event.
proof fn lemma_covers_start<'m, M: Model>(m: M, init: M::State, trace: Seq<Ev<M>>, set: Seq<Config<'m, M>>, ids: Seq<CallId>)
    requires
        set.len() > 0,
        set[0]@ == semantics::initial::<M>(init),
        closed(m, set, ids),
        invoked::<M>(trace, ids),
    ensures
        covers(m, init, trace, 0, set),
{
    let first = semantics::initial::<M>(init);
    assert forall|c: Cfg<M>| #[trigger] reach(m, init, trace, 0, c) implies in_set(set, c) by {
        let steps = choose|steps: Execution<M>|
            #![trigger semantics::legal(m, first, steps), semantics::project::<M>(steps)]
            semantics::legal(m, first, steps) && semantics::project::<M>(steps) == trace.subrange(0, 0)
                && semantics::before::<M>(first, steps, steps.len() as int) == c;
        lemma_labels_in::<M>(steps, trace, 0, ids);
        lemma_labels_shown::<M>(steps);
        assert forall|i: int| 0 <= i < steps.len() implies #[trigger] steps[i].0 is Silent by {
            if let Label::Obs(e) = steps[i].0 {
                assert(semantics::project::<M>(steps).contains(e));
            }
        }
        assert forall|i: int| 0 <= i <= steps.len() implies keys_in::<M>(#[trigger] semantics::before::<M>(first, steps, i), ids) by {
            lemma_keys(m, first, steps, ids, i);
        }
        assert(in_set(set, first)) by {
            assert(set[0]@ == first);
        }
        lemma_silent_tail(m, first, steps, 0, set, ids);
    }
}

/// From a set covering the configurations after `k` events, the configurations
/// showing event `k` from them, closed, cover those after `k + 1`.
proof fn lemma_covers_next<'m, M: Model>(
    m: M,
    init: M::State,
    trace: Seq<Ev<M>>,
    k: int,
    ids: Seq<CallId>,
    entered: Seq<Config<'m, M>>,
    set: Seq<Config<'m, M>>,
)
    requires
        0 <= k < trace.len(),
        invoked::<M>(trace, ids),
        // every configuration reachable after k events, observing event k, lands in `entered`
        forall|c: Cfg<M>, d: Cfg<M>|
            #[trigger] reach(m, init, trace, k, c) && #[trigger] semantics::step(m, c, Label::Obs(trace[k]), d) ==> in_set(entered, d),
        grows(entered, set),
        closed(m, set, ids),
    ensures
        covers(m, init, trace, k + 1, set),
{
    let first = semantics::initial::<M>(init);
    assert forall|c: Cfg<M>| #[trigger] reach(m, init, trace, k + 1, c) implies in_set(set, c) by {
        let steps = choose|steps: Execution<M>|
            #![trigger semantics::legal(m, first, steps), semantics::project::<M>(steps)]
            semantics::legal(m, first, steps) && semantics::project::<M>(steps) == trace.subrange(0, k + 1)
                && semantics::before::<M>(first, steps, steps.len() as int) == c;
        let n = lemma_split::<M>(steps, k);
        assert(semantics::project::<M>(steps)[k] == trace[k]);
        let pre = steps.subrange(0, n);
        lemma_prefix(m, first, steps, n);
        assert(semantics::project::<M>(pre) =~= trace.subrange(0, k));
        let b = semantics::before::<M>(first, steps, n);
        assert(semantics::before::<M>(first, pre, pre.len() as int) == b);
        assert(reach(m, init, trace, k, b));
        assert(semantics::step(m, b, steps[n].0, steps[n].1));
        assert(semantics::before::<M>(first, steps, n + 1) == steps[n].1);
        assert(in_set(entered, steps[n].1));
        lemma_in_set_grows(entered, set, steps[n].1);
        lemma_labels_in::<M>(steps, trace, k + 1, ids);
        assert forall|i: int| n + 1 <= i <= steps.len() implies keys_in::<M>(#[trigger] semantics::before::<M>(first, steps, i), ids) by {
            lemma_keys(m, first, steps, ids, i);
        }
        lemma_silent_tail(m, first, steps, n + 1, set, ids);
    }
}

/// No configuration reachable after `k` events can show event `k`: the trace
/// is not valid.
proof fn lemma_stuck<'m, M: Model>(m: M, init: M::State, trace: Seq<Ev<M>>, k: int, set: Seq<Config<'m, M>>, next: Seq<Config<'m, M>>)
    requires
        0 <= k < trace.len(),
        covers(m, init, trace, k, set),
        forall|i2: int, d: Cfg<M>|
            #![trigger set[i2], semantics::step(m, set[i2]@, Label::Obs(trace[k]), d)]
            0 <= i2 < set.len() && semantics::step(m, set[i2]@, Label::Obs(trace[k]), d) ==> in_set(next, d),
        next.len() == 0,
    ensures
        !semantics::valid(m, init, trace),
{
    let first = semantics::initial::<M>(init);
    if semantics::valid(m, init, trace) {
        let steps = choose|steps: Execution<M>|
            #![trigger semantics::legal(m, first, steps), semantics::project::<M>(steps)]
            semantics::legal(m, first, steps) && semantics::project::<M>(steps) == trace;
        let n0 = lemma_prefix_showing::<M>(steps, k);
        let pre = steps.subrange(0, n0);
        lemma_prefix(m, first, steps, n0);
        assert(semantics::project::<M>(pre) == trace.subrange(0, k + 1));
        let n = lemma_split::<M>(pre, k);
        assert(semantics::project::<M>(pre)[k] == trace[k]);
        let pre2 = pre.subrange(0, n);
        lemma_prefix(m, first, pre, n);
        assert(semantics::project::<M>(pre2) =~= trace.subrange(0, k));
        let b = semantics::before::<M>(first, pre, n);
        assert(semantics::before::<M>(first, pre2, pre2.len() as int) == b);
        assert(reach(m, init, trace, k, b));
        let q = choose|q: int| #![trigger set[q]] 0 <= q < set.len() && set[q]@ == b;
        assert(semantics::step(m, b, pre[n].0, pre[n].1));
        assert(semantics::step(m, set[q]@, Label::Obs(trace[k]), pre[n].1));
        assert(in_set(next, pre[n].1));
    }
}

} // verus!
