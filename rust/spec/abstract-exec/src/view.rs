//! Views of executable model records.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use echod_rover::rover::comm::Sched;
use echod_types::Schedule;
use crate::machine::*;
use crate::trusted::*;
pub use echod_abstract_spec::view::*;

verus! {
impl View for Promise {
    type V = PromiseV;

    open spec fn view(&self) -> PromiseV {
        PromiseV {
            state: self.state,
            value: self.value,
            param: self.param,
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
            tags: self.tags,
            callbacks: self.callbacks@,
            listeners: self.listeners@,
        }
    }
}

impl View for Task {
    type V = TaskV;

    open spec fn view(&self) -> TaskV {
        TaskV {
            state: self.state,
            version: self.version,
            pid: ostr(self.pid),
            ttl: self.ttl,
            acquired_at: self.acquired_at,
            retry_timeout_at: self.retry_timeout_at,
            resumes: strs(self.resumes@),
        }
    }
}

impl View for Store {
    type V = StoreV;

    open spec fn view(&self) -> StoreV {
        StoreV {
            promises: self.promises@.map_values(|p: Promise| p@),
            tasks: self.tasks@.map_values(|t: Task| t@),
            schedules: self.schedules@.map_values(|c: Schedule| schedule_v(c)),
        }
    }
}

impl View for Work {
    type V = InternalV;

    open spec fn view(&self) -> InternalV {
        match self {
            Work::PromiseTimeout(id) => InternalV::PromiseTimeout(id@),
            Work::Callback { awaited, awaiter } => InternalV::Callback { awaited: awaited@, awaiter: awaiter@ },
            Work::Listener { awaited, address } => InternalV::Listener { awaited: awaited@, address: address@ },
            Work::TaskLeaseTimeout(id) => InternalV::TaskLeaseTimeout(id@),
            Work::TaskRetryTimeout(id) => InternalV::TaskRetryTimeout(id@),
            Work::ScheduleTimeout { id, promise } => InternalV::ScheduleTimeout { id: id@, promise: promise@ },
            Work::Occurrence { promise, at, timeout, param, tags } => InternalV::Occurrence {
                promise: promise@,
                at: *at,
                timeout: *timeout,
                param: *param,
                tags: *tags,
            },
        }
    }
}

/// An occurrence is a timer at its instant. Anything else is later, and the
/// checker derives those from the maps instead of the queue.
pub open spec fn as_sched(w: Work) -> Sched<InternalV> {
    match w {
        Work::Occurrence { promise, at, timeout, param, tags } => Sched::Timer(
            at,
            InternalV::Occurrence { promise: promise@, at, timeout, param, tags },
        ),
        Work::PromiseTimeout(id) => Sched::Later(InternalV::PromiseTimeout(id@)),
        Work::Callback { awaited, awaiter } => Sched::Later(InternalV::Callback { awaited: awaited@, awaiter: awaiter@ }),
        Work::Listener { awaited, address } => Sched::Later(InternalV::Listener { awaited: awaited@, address: address@ }),
        Work::TaskLeaseTimeout(id) => Sched::Later(InternalV::TaskLeaseTimeout(id@)),
        Work::TaskRetryTimeout(id) => Sched::Later(InternalV::TaskRetryTimeout(id@)),
        Work::ScheduleTimeout { id, promise } => Sched::Later(InternalV::ScheduleTimeout { id: id@, promise: promise@ }),
    }
}

/// An internal item of the checker's, as a view.
pub open spec fn sched_v(s: Sched<Work>) -> Sched<InternalV> {
    match s {
        Sched::Later(r) => Sched::Later(r@),
        Sched::Timer(t, r) => Sched::Timer(t, r@),
    }
}

pub open spec fn works(v: Seq<Work>) -> Seq<Sched<InternalV>> {
    v.map_values(|w: Work| as_sched(w))
}

pub open spec fn sends(v: Seq<Dispatch>) -> Seq<DispatchV> {
    v.map_values(|d: Dispatch| d@)
}

impl View for Out {
    type V = OutV;

    open spec fn view(&self) -> OutV {
        OutV { resp: self.resp, next: self.next@, work: works(self.work@), send: sends(self.send@) }
    }
}

impl View for InOut {
    type V = InOutV;

    open spec fn view(&self) -> InOutV {
        InOutV { next: self.next@, work: works(self.work@), send: sends(self.send@), not_due: self.not_due }
    }
}

pub open spec fn outs_v(v: Seq<Out>) -> Seq<OutV> {
    v.map_values(|o: Out| o@)
}

pub broadcast proof fn lemma_works_len(v: Seq<Work>)
    ensures
        #[trigger] works(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_works_index(v: Seq<Work>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] works(v)[i] == as_sched(v[i]),
{
}

pub broadcast proof fn lemma_sends_len(v: Seq<Dispatch>)
    ensures
        #[trigger] sends(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_sends_index(v: Seq<Dispatch>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] sends(v)[i] == v[i]@,
{
}

pub broadcast proof fn lemma_works_empty(v: Seq<Work>)
    requires
        v.len() == 0,
    ensures
        #[trigger] works(v) == Seq::<Sched<InternalV>>::empty(),
{
    assert(works(v) =~= Seq::<Sched<InternalV>>::empty());
}

pub broadcast proof fn lemma_sends_empty(v: Seq<Dispatch>)
    requires
        v.len() == 0,
    ensures
        #[trigger] sends(v) == Seq::<DispatchV>::empty(),
{
    assert(sends(v) =~= Seq::<DispatchV>::empty());
}

pub broadcast proof fn lemma_outs_len(v: Seq<Out>)
    ensures
        #[trigger] outs_v(v).len() == v.len(),
{
}

pub broadcast proof fn lemma_outs_index(v: Seq<Out>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] outs_v(v)[i] == v[i]@,
{
}

pub broadcast group group_views {
    lemma_works_len, lemma_works_index, lemma_sends_len, lemma_sends_index,
    lemma_works_empty, lemma_sends_empty, lemma_outs_len, lemma_outs_index,
    lemma_strs_len, lemma_strs_index, lemma_strs_empty,
    lemma_mv_empty, lemma_mv_push, lemma_mv_add, lemma_mv_take,
    lemma_map_values_insert, lemma_map_values_remove, axiom_pset_seq,
}

} // verus!
