//! The Abstract's internal actions as spec values, and runs of them.
//!
//! `echod_abstract::system::InternalAction` is the executable vocabulary;
//! this is its ghost twin, with the effects each action has by the
//! Abstract's own `*_semantics`. A kernel step simulates to a run of these.

use vstd::prelude::*;

use echod_abstract::internal as aint;
use echod_abstract::state::{AEffect, AState, spec_apply_all};
use echod_abstract::types as abs;

use crate::read_sim::lemma_apply_all_app;
use crate::*;

verus! {

pub enum AbsInternal {
    PromiseTimeout(abs::APromiseTimeoutReq),
    Callback(abs::APromiseRegisterCallbackReq),
    Listener(abs::APromiseRegisterListenerReq),
    TaskLeaseTimeout(abs::ATaskLeaseTimeoutReq),
    TaskRetryTimeout(abs::ATaskRetryTimeoutReq),
    ScheduleFire(abs::AScheduleFireReq),
    ScheduleAdvance(abs::AScheduleAdvanceReq),
}

/// The effects of one internal action on `a` at `now`; `retry_timeout` is
/// the configuration's.
pub open spec fn internal_effects(a: AState, act: AbsInternal, now: u64, retry_timeout: u64) -> Seq<AEffect> {
    match act {
        AbsInternal::PromiseTimeout(q) => aint::promise_timeout_semantics(a, q, now),
        AbsInternal::Callback(q) => aint::callback_semantics(a, q, now),
        AbsInternal::Listener(q) => aint::listener_semantics(a, q, now),
        AbsInternal::TaskLeaseTimeout(q) => aint::lease_timeout_semantics(a, q, now),
        AbsInternal::TaskRetryTimeout(q) => aint::retry_timeout_semantics(a, q, now, retry_timeout),
        AbsInternal::ScheduleFire(q) => aint::schedule_fire_semantics(a, q, now),
        AbsInternal::ScheduleAdvance(q) => aint::schedule_advance_semantics(a, q, now),
    }
}

pub open spec fn internal_step(a: AState, act: AbsInternal, now: u64, retry_timeout: u64) -> AState {
    spec_apply_all(a, internal_effects(a, act, now, retry_timeout))
}

/// The actions run in order, each on the state the one before left.
pub open spec fn internal_run(a: AState, acts: Seq<AbsInternal>, now: u64, retry_timeout: u64) -> AState
    decreases acts.len(),
{
    if acts.len() == 0 {
        a
    } else {
        internal_run(internal_step(a, acts[0], now, retry_timeout), acts.drop_first(), now, retry_timeout)
    }
}

pub proof fn lemma_internal_run_app(a: AState, s: Seq<AbsInternal>, t: Seq<AbsInternal>, now: u64, rt: u64)
    ensures internal_run(a, s + t, now, rt) == internal_run(internal_run(a, s, now, rt), t, now, rt),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s + t =~= t);
    } else {
        assert((s + t)[0] == s[0]);
        assert((s + t).drop_first() =~= s.drop_first() + t);
        lemma_internal_run_app(internal_step(a, s[0], now, rt), s.drop_first(), t, now, rt);
    }
}

pub proof fn lemma_internal_run_one(a: AState, act: AbsInternal, now: u64, rt: u64)
    ensures internal_run(a, seq![act], now, rt) == internal_step(a, act, now, rt),
{
    let s = seq![act];
    assert(s.len() == 1 && s[0] == act);
    assert(s.drop_first() =~= Seq::<AbsInternal>::empty());
    assert(internal_run(a, s, now, rt) == internal_run(internal_step(a, act, now, rt), s.drop_first(), now, rt));
}

pub proof fn lemma_internal_run_push(a: AState, s: Seq<AbsInternal>, act: AbsInternal, now: u64, rt: u64)
    ensures internal_run(a, s.push(act), now, rt) == internal_step(internal_run(a, s, now, rt), act, now, rt),
{
    assert(s.push(act) =~= s + seq![act]);
    lemma_internal_run_app(a, s, seq![act], now, rt);
    lemma_internal_run_one(internal_run(a, s, now, rt), act, now, rt);
}

} // verus!
