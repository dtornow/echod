//! `Concrete`, the store machine, as an `accordant::Model`.

use vstd::prelude::*;

use accordant::semantics::{ExternalOutcomeV, InternalOutcomeV};
use accordant::{ExternalOutcome, InternalOutcome, Model, Sched, Time};
use echod_kernel::external::spec_handle;
use echod_kernel::store::AState;
use echod_kernel::types::*;
use resonate::twins::*;
use resonate::{Dispatch, Request, Response};

use crate::sweep::{next_deadline, sweep_fn, sweep_sends};
use crate::translate::*;

verus! {

/// The bucket: the kernel's state, held as a ghost value. Nothing here runs;
/// the machine exists for its twins.
pub struct Store {
    pub a: Ghost<AState>,
}

impl View for Store {
    type V = AState;

    open spec fn view(&self) -> AState {
        self.a@
    }
}

/// The store with this contents: `axiom_store_realised` says one exists.
pub open spec fn lift_store(a: AState) -> Store {
    choose|s: Store| s@ == a
}

#[verifier::external_body]
pub proof fn axiom_store_realised(a: AState)
    ensures
        lift_store(a)@ == a,
{
}

/// The store machine's internal work: a sweep of the bucket at the clock.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum CStep {
    Sweep,
}

impl View for CStep {
    type V = CStep;

    open spec fn view(&self) -> CStep {
        *self
    }
}

/// The store machine, with the one dial the kernel's `Config` has that the
/// protocol reads: the redispatch cadence.
pub struct Concrete {
    pub retry_timeout: u64,
}

/// The step begins with an empty outbox: what a step leaves there, it sends.
pub open spec fn fresh(a: AState) -> AState {
    AState { outbox: Map::empty(), ..a }
}

/// The key a commit arms: a sweep at the state's next deadline.
pub open spec fn arm(a: AState) -> Seq<Sched<CStep>> {
    match next_deadline(a) {
        Some(t) => seq![Sched::Timer(t as u64, CStep::Sweep)],
        None => Seq::empty(),
    }
}

pub open spec fn lift_dispatches(ds: Seq<DispatchV>) -> Seq<Dispatch> {
    ds.map_values(|d: DispatchV| lift_dispatch(d))
}

pub open spec fn outcome(a: AState, resp: ResponseV, send: Seq<DispatchV>) -> ExternalOutcomeV<Store, Response, CStep, Dispatch> {
    ExternalOutcomeV { next: lift_store(fresh(a)), resp: lift_response(resp), work: arm(a), send: lift_dispatches(send) }
}

impl Concrete {
    /// A request takes effect: the wire rules; a sweep at the instant; the
    /// handler; a drain. A detached create is two of those, the create in its
    /// origin and then the fence's check in the task's, the check's status
    /// deciding the answer.
    pub open spec fn request(&self, req: RequestV, a0: AState, now: Time) -> ExternalOutcomeV<Store, Response, CStep, Dispatch> {
        let t = self.retry_timeout as nat;
        let a = fresh(a0);
        let n = now as nat;
        match plan(req) {
            Plan::Refuse(code) => outcome(a, ResponseV::Status(code), Seq::empty()),
            Plan::One(kreq) => {
                let (b, r) = spec_handle(sweep_fn(a, n, t), kreq, n);
                outcome(sweep_fn(b, n, t), response_out(r), sweep_sends(a, n, t) + sweep_sends(b, n, t))
            },
            Plan::Detached(create, check) => {
                let (b, r1) = spec_handle(sweep_fn(a, n, t), ARequest::PromiseCreate(create), n);
                let (c, r2) = spec_handle(sweep_fn(b, n, t), ARequest::TaskFenceCheck(check), n);
                let resp = match r2 {
                    AResponse::Status(s) => if s.status != 200 { ResponseV::Status(s.status) } else { response_out(r1) },
                    _ => response_out(r1),
                };
                outcome(sweep_fn(c, n, t), resp, sweep_sends(a, n, t) + sweep_sends(b, n, t) + sweep_sends(c, n, t))
            },
        }
    }

    /// A sweep runs: everything due on the bucket at the clock.
    pub open spec fn sweep(&self, a0: AState, now: Time) -> InternalOutcomeV<Store, CStep, Dispatch> {
        let a = sweep_fn(fresh(a0), now as nat, self.retry_timeout as nat);
        InternalOutcomeV { next: lift_store(fresh(a)), work: arm(a), send: lift_dispatches(sweep_sends(fresh(a0), now as nat, self.retry_timeout as nat)) }
    }
}

impl Model for Concrete {
    type State = Store;

    type External = Request;

    type Response = Response;

    type Internal = CStep;

    type Dispatch = Dispatch;

    open spec fn spec_external(&self, req: Request, state: Store, now: Time) -> Seq<ExternalOutcomeV<Store, Response, CStep, Dispatch>> {
        seq![self.request(req@, state@, now)]
    }

    open spec fn spec_internal(&self, req: CStep, state: Store, now: Time) -> Seq<InternalOutcomeV<Store, CStep, Dispatch>> {
        seq![self.sweep(state@, now)]
    }

    /// Nothing runs: the store machine is its twins.
    #[verifier::external_body]
    fn external(&self, op: &Request, s: &Store, now: Time) -> (r: Vec<ExternalOutcome<Self>>) {
        unimplemented!()
    }

    #[verifier::external_body]
    fn internal(&self, step: &CStep, s: &Store, now: Time) -> (r: Vec<InternalOutcome<Self>>) {
        unimplemented!()
    }
}

/// The empty bucket.
pub open spec fn concrete_init() -> AState {
    AState { objects: Map::empty(), schedules: Map::empty(), outbox: Map::empty() }
}

} // verus!

// The traits the checker's `Model` asks of a state, for a value nothing runs
// on. Every store is equal to every other here: the machine's identity is
// its ghost contents, which the proofs compare; no checker ever holds one.
#[verifier::external]
impl Clone for Store {
    fn clone(&self) -> Self {
        Store { a: self.a }
    }
}

#[verifier::external]
impl PartialEq for Store {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

#[verifier::external]
impl Eq for Store {}

#[verifier::external]
impl std::hash::Hash for Store {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

#[verifier::external]
impl std::fmt::Debug for Store {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Store")
    }
}
